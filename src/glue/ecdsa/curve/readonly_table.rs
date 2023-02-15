use franklin_crypto::plonk::circuit::permutation_network::*;
use crate::vm::primitives::UInt16;
use std::collections::HashMap;

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct ReadOnlyTable<E: Engine, const N: usize>{
    pub range_infos: [Option<usize>; N],
    pub queries: Vec<(UInt16<E>, [Num<E>; N])>,
    pub witness_map: HashMap<u16, [E::Fr; N]>
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
    pub fn place_initial_values(&mut self, values: &[(UInt16<E>, [Num<E>; N])]){
        assert!(values.len() < (1<<16), "code is too long");
        for (index, vals) in values.iter() {
            match (index.get_value(), Num::get_value_multiple(&vals)) {
                (Some(index), Some(vals)) => {
                    assert!(self.witness_map.get(&index).is_none());
                    self.witness_map.insert(index, vals);
                },
                _ => {}
            }

            self.queries.push((*index, *vals));
        }
    }
    
    #[track_caller]
    pub fn get_witness_for_read<CS: ConstraintSystem<E>>(&self, cs: &mut CS, at: UInt16<E>) -> Result<[Num<E>; N], SynthesisError> {
        let witness = if let Some(at) = at.get_value() {
            if let Some(value) = self.witness_map.get(&at) {
                Some(*value)
            } else {
                panic!("reading from unknown location at index {}", at);
            }
        } else {
            None
        };

        let value = Num::alloc_multiple(cs, witness)?;

        Ok(value)
    }

    #[track_caller]
    pub fn read<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, at: UInt16<E>) -> Result<[Num<E>; N], SynthesisError> {
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

        let len = self.range_infos.len() + 1;
        let mut items = vec![];
        items.push((0, Some(16usize)));
        for el in self.range_infos.iter() {
            let idx = items.len();
            items.push((idx, *el));
        }
        assert_eq!(items.len(), len);

        let mut everything_as_nums = vec![];
        for (at, value) in self.queries.iter() {
            let mut tmp = vec![];
            tmp.push(at.inner);
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
        let mut previous_cell_index = UInt16::from_num_unchecked(previous_cell_index);

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
            let cell_index = UInt16::from_num_unchecked(cell_index);

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

    fn calculate_permutation(els: &Vec<(UInt16<E>, [Num<E>; N])>) -> Option<IntegerPermutation> {
        // we have to sort it based on the index, then PC

        let mut keys = vec![];
        for (at, _) in els.iter() {
            if let Some(at) = at.get_value() {
                let composite_key = at;
                let idx = keys.len();
                keys.push((idx, composite_key));
            } else {
                return None
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

pub fn enforce_packed_readonly_permutations<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    permutation: IntegerPermutation,
    original_unpacked_values: Vec<Vec<Num<E>>>,
    ranges_info: Vec<(usize, Option<usize>)>
) -> Result<Vec<Vec<(usize, Option<usize>, Num<E>)>>, SynthesisError> {
    let switches = order_into_switches_set(cs, &permutation)?;

    let mut required_elements = None;
    let mut strategy = None;

    let capacity = E::Fr::CAPACITY as usize;

    use itertools::Itertools;

    let len = ranges_info.len();
    // brute force, lol
    for permutation in ranges_info.iter().permutations(len) {
        let mut num_used = 0;
        let mut remaining = capacity;
        let mut order: Vec<Vec<usize>> = vec![];
        let mut subset: Vec<usize> = vec![];
        for &(idx, el) in permutation.iter() {
            if let Some(required_len) = el {
                if remaining >= *required_len {
                    remaining -= required_len;
                    subset.push(*idx);
                } else {
                    order.push(subset);
                    num_used += 1;
                    subset = vec![];
                    remaining = capacity;
                    remaining -= required_len;
                    subset.push(*idx);
                }
            } else {
                if !subset.is_empty() {
                    order.push(subset);
                } 
                // we need to take a full element
                num_used += 1;
                order.push(vec![*idx]);

                remaining = capacity;
                subset = vec![];
            }
        }

        if !subset.is_empty() {
            order.push(subset);
            num_used += 1;
        } 

        if let Some(num_els) = required_elements {
            if num_used < num_els {
                required_elements = Some(num_used);
                strategy = Some(order);
            }
        } else {
            required_elements = Some(num_used);
            strategy = Some(order);
        }
    }

    let strategy = strategy.expect("some strategy must be made");

    let mut original_values_sets_unpacked: Vec<Vec<_>> = vec![];
    let mut original_values_sets: Vec<Vec<Num<E>>> = vec![];
    let mut sorted_values_sets: Vec<Vec<Num<E>>> = vec![];

    // now we should be clever and pack everything as tight as possible!

    let shift = compute_shifts::<E::Fr>();

    for row in original_unpacked_values.iter() {
        let mut packed_set = vec![];
        let mut unpacked_set = vec![];
        for subset in strategy.iter() {
            let mut lc = LinearCombination::zero();
            let mut shift_in_bits = 0;
            for &idx in subset.iter() {
                let el = row[idx];
                let (expected_idx, length) = ranges_info[idx];
                assert_eq!(expected_idx, idx);
                unpacked_set.push((idx, length, el));

                let shift = shift[shift_in_bits];
                lc.add_assign_number_with_coeff(&el, shift);

                if let Some(width) = length {
                    shift_in_bits += width;
                } else {
                    unimplemented!()
                }
            }
            let num = lc.into_num(cs)?;
            packed_set.push(num);
        }
        original_values_sets_unpacked.push(unpacked_set);
        original_values_sets.push(packed_set);
    }

    let mut sorted_unpacked: Vec<Vec<(usize, Option<usize>, Num<E>)>> = vec![];

    for index in permutation.elements.iter() {
        let original_values_set_for_witnessing = &original_values_sets_unpacked[*index];
        // reallocate
        let mut sorted_reallocated = vec![];
        for (idx, length, el) in original_values_set_for_witnessing.iter() {
            let reallocated = Num::alloc(cs, el.get_value())?;
            if let Some(width) = *length {
                constraint_bit_length(cs, &el, width)?;
            } else {
                unimplemented!()
            }
            sorted_reallocated.push((*idx, *length, reallocated));
        }
        sorted_unpacked.push(sorted_reallocated);
    }

    assert_eq!(sorted_unpacked.len(), original_values_sets_unpacked.len());
    // repack and range check

    for values in sorted_unpacked.iter() {
        let mut packed_set = vec![];
        for subset in strategy.iter() {
            let mut lc = LinearCombination::zero();
            let mut shift_in_bits = 0;
            for &idx in subset.iter() {
                let (eidx, elength, el) = values[idx];
                let (expected_idx, length) = ranges_info[idx];
                assert_eq!(expected_idx, idx);
                assert_eq!(eidx, idx);
                assert_eq!(elength, length);

                let shift = shift[shift_in_bits];
                lc.add_assign_number_with_coeff(&el, shift);

                if let Some(width) = length {
                    shift_in_bits += width;
                }
            }
            let num = lc.into_num(cs)?;
            packed_set.push(num);
        }
        sorted_values_sets.push(packed_set);
    }

    assert_eq!(original_values_sets.len(), sorted_values_sets.len());

    // prove some permutation

    let num_subsets = strategy.len();
    for i in 0..num_subsets {
        // collect separately
        let o: Vec<_> = original_values_sets.iter().map(|el| el[i]).collect();
        let s: Vec<_> = sorted_values_sets.iter().map(|el| el[i]).collect();

        prove_permutation_of_nums_using_switches_witness(
            cs, 
            &s[..],
            &o[..],
            &switches
        )?;
    }

    Ok(sorted_unpacked)
}