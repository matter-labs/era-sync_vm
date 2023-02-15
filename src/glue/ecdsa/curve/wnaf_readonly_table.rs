use franklin_crypto::plonk::circuit::permutation_network::*;
use crate::vm::primitives::uint16::*;
use std::collections::HashMap;
use super::readonly_table::enforce_packed_readonly_permutations;

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct ReadOnlyTable<E: Engine, const N: usize>{
    pub range_infos: [Option<usize>; N],
    pub queries: Vec<((Boolean, UInt16<E>), [Num<E>; N])>,
    pub witness_map: HashMap<(bool, u16), [E::Fr; N]>
}

impl<E: Engine, const N: usize> ReadOnlyTable<E, N> {
    pub fn new_for_range_parameters(range_infos: [Option<usize>; N]) -> Self {
        Self {
            range_infos,
            queries: vec![],
            witness_map: HashMap::new()
        }
    }

    #[track_caller]
    pub fn place_initial_values(&mut self, values: &[((Boolean, UInt16<E>), [Num<E>; N])]){
        assert!(values.len() < (1<<16), "code is too long");
        for ((sign_flag, index), vals) in values.iter() {
            match (sign_flag.get_value(), index.get_value(), Num::get_value_multiple(&vals)) {
                (Some(sign_flag), Some(index), Some(vals)) => {
                    // create composite insed
                    // let composite_index = (sign_flag as u16) << 15 + index;
                    assert!(self.witness_map.get(&(sign_flag, index)).is_none());
                    self.witness_map.insert((sign_flag, index), vals);
                },
                _ => {}
            }

            self.queries.push(((*sign_flag, *index), *vals));
        }
    }
    
    pub fn get_witness_for_read<CS: ConstraintSystem<E>>(&self, cs: &mut CS, at: (Boolean, UInt16<E>)) -> Result<[Num<E>; N], SynthesisError> {
        let witness = match (at.0.get_value(), at.1.get_value()) {
            (Some(sign_flag), Some(index)) => {
                let value = self.witness_map.get(&(sign_flag, index)).expect("read must happen from known location").clone();
                Some(value)
            },
            _ => None
        };

        let value = Num::alloc_multiple(cs, witness)?;

        Ok(value)
    }

    pub fn read<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, at: (Boolean, UInt16<E>)) -> Result<[Num<E>; N], SynthesisError> {
        let value = self.get_witness_for_read(cs, at.clone())?;
        self.queries.push((at, value));

        Ok(value)
    }

    pub fn enforce_validity_optimized<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // we only need to sort by keys, because we know that after initialization
        // an vitrual timestep = 0 we no longer have reads

        // even though we use timestamp in a sorting function for witness, we do not check timestamps in a circuit
        let size = self.queries.len();
        let permutation = Self::calculate_permutation(&self.queries);
        let permutation = if let Some(permutation) = permutation {
            permutation
        } else {
            // create dummy
            IntegerPermutation::new(size)
        };


        // we use 16 here for now
        let len = self.range_infos.len() + 1;
        let mut items = vec![];
        items.push((0, Some(16usize)));
        for el in self.range_infos.iter() {
            let idx = items.len();
            items.push((idx, *el));
        }

        let shifts = compute_shifts::<E::Fr>();

        // repack keys during the process
        let mut everything_as_nums = vec![];
        for ((sign_flag, index), value) in self.queries.iter() {
            let mut tmp = vec![];
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&index.inner, shifts[0]);
            lc.add_assign_boolean_with_coeff(&sign_flag, shifts[15]);
            let key = lc.into_num(cs)?;
            tmp.push(key);
            tmp.extend_from_slice(value);
            everything_as_nums.push(tmp);
        }

        let num_rows = everything_as_nums.len();

        let sorted_unpacked = enforce_packed_readonly_permutations(
            cs,
            permutation,
            everything_as_nums,
            items
        )?;

        assert_eq!(sorted_unpacked.len(), num_rows);

        // now walk over the sorted set and enforce a logic
        // here we treat element 0 that is a packed key as a simple integer
        let mut it = sorted_unpacked.into_iter();

        let previous_unpacked_set = it.next().expect("must contain at least 1 value");
        let mut previous_unpacked_values = vec![];
        let mut previous_cell_index = None;
        for (idx, _, el) in previous_unpacked_set {
            if idx == 0 {
                previous_cell_index = Some(el);
            } else {
                previous_unpacked_values.push(el);
            }
        }
        let previous_cell_index = previous_cell_index.expect("is some");
        let mut previous_cell_index = UInt16::from_num_unchecked(previous_cell_index)?;

        for unpacked_set in it 
        {
            let mut unpacked_values = vec![];
            let mut cell_index = None;
            for (idx, _, el) in unpacked_set {
                if idx == 0 {
                    cell_index = Some(el);
                } else {
                    unpacked_values.push(el);
                }
            }
            let cell_index = cell_index.expect("is some");
            let cell_index = UInt16::from_num_unchecked(cell_index)?;

            let (cell_idx_difference, borrow) = cell_index.sub(cs, &previous_cell_index)?;
            Boolean::enforce_equal(cs, &borrow, &Boolean::constant(false))?;
            let new_cell = cell_idx_difference.is_zero(cs)?.not();

            let mut bools = vec![];
            for (previous, this) in previous_unpacked_values.iter().zip(unpacked_values.iter()) {
                let unchanged = Num::equals(cs, &previous, &this)?;
                bools.push(unchanged);
            }

            let unchanged = smart_and(cs, &bools)?;

            // validity table
            // new cell | unchanged 
            //    0     |     1     // read old cell
            //    1     |     0     // read new cell, check for 0
            can_not_be_false_if_flagged(cs, &unchanged, &new_cell.not())?;

            previous_cell_index = cell_index;
            previous_unpacked_values = unpacked_values;
        }

        Ok(())
    }

    fn calculate_permutation(els: &Vec<((Boolean, UInt16<E>), [Num<E>; N])>) -> Option<IntegerPermutation> {
        // we have to sort it based on the index, then PC

        let mut keys = vec![];
        for ((sign_flag, at), _) in els.iter() {
            match (sign_flag.get_value(), at.get_value()) {
                (Some(sign_flag), Some(index)) => {
                    let composite_key = (sign_flag as u16) << 15 + index;
                    let idx = keys.len();
                    keys.push((idx, composite_key));
                },
                _ => {
                    return None
                }
            }
        }

        // we have all the keys, so let's sort it
        // based on the composite key, and get indexes for free
        keys.sort_by(|a, b| a.1.cmp(&b.1));
        let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();

        let integer_permutation = IntegerPermutation::new_from_permutation(integer_permutation);

        Some(integer_permutation)
    }
}