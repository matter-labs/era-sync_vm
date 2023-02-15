use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;

use super::traits::*;
use super::*;
use crate::derivative::*;
use crate::ConstraintSystem;

#[derive(Clone, Debug)]
pub struct MerklePathWitness<E: Engine> {
    inner: Vec<Num<E>>,
}

impl<E: Engine> MerklePathWitness<E> {
    pub fn new_for_size<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Vec<E::Fr>>,
        size: usize,
    ) -> Result<Self, SynthesisError> {
        if let Some(vec) = witness.as_ref() {
            assert!(vec.len() >= size, "witness size is too small");
        }
        let mut allocated = Vec::with_capacity(size);
        for idx in 0..size {
            let witness = if let Some(vec) = witness.as_ref() {
                Some(vec[idx])
            } else {
                None
            };

            let el = AllocatedNum::alloc(cs, || Ok(*witness.get()?))?;

            allocated.push(Num::Variable(el));
        }

        Ok(Self::new_from_allocated(allocated))
    }

    pub fn new_from_allocated(allocated: Vec<Num<E>>) -> Self {
        Self { inner: allocated }
    }

    pub fn new_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Vec<Option<E::Fr>>,
    ) -> Result<Self, SynthesisError> {
        let mut allocated = Vec::with_capacity(witness.len());
        for witness in witness.into_iter() {
            let el = AllocatedNum::alloc(cs, || Ok(*witness.get()?))?;

            allocated.push(Num::Variable(el));
        }

        Ok(Self::new_from_allocated(allocated))
    }

    pub fn witness(&self) -> &[Num<E>] {
        &self.inner
    }
}

// pub fn calculate_to_root<E: Engine, CS: ConstraintSystem<E>, H: CircuitArithmeticCommitter<E>>(
//     cs: &mut CS,
//     leaf_hash: &Num<E>,
//     path_wittnes: &MerklePathWitness<E>,
//     path: &[Boolean],
//     committer: &H,
// ) -> Result<AllocatedNum<E>, SynthesisError> {
//     assert_eq!(path.len(), path_wittnes.witness().len());

//     let wit = path_wittnes.witness();

//     let mut current = leaf_hash.clone();

//     for (path_bit, witness_value) in path.iter().zip(wit.iter()) {
//         current = hash_to_node(cs, path_bit, &current, &witness_value, committer)?;
//     }

//     let as_allocated = current.get_variable();

//     Ok(as_allocated)
// }

// pub fn calculate_to_root_fixed<E: Engine, CS: ConstraintSystem<E>, H: CircuitArithmeticCommitter<E>, const N: usize>(
//     cs: &mut CS,
//     leaf_hash: &Num<E>,
//     path_witness: &[Num<E>; N],
//     path: &[Boolean; N],
//     committer: &H,
// ) -> Result<Num<E>, SynthesisError> {
//     let mut current = leaf_hash.clone();

//     for (path_bit, witness_value) in path.iter().zip(path_witness.iter()) {
//         current = hash_to_node(cs, path_bit, &current, &witness_value, committer)?;
//     }

//     Ok(current)
// }

pub fn calculate_to_root_fixed_with_round_function<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const N: usize,
>(
    cs: &mut CS,
    leaf_hash: &Num<E>,
    path_witness: &[Num<E>; N],
    path: &[Boolean; N],
    round_function: &R,
) -> Result<Num<E>, SynthesisError> {
    let mut current = leaf_hash.clone();

    for (path_bit, witness_value) in path.iter().zip(path_witness.iter()) {
        current = hash_to_node_with_round_function(
            cs,
            path_bit,
            &current,
            &witness_value,
            round_function,
        )?;
    }

    Ok(current)
}

// fn hash_to_node<E: Engine, CS: ConstraintSystem<E>, H: CircuitArithmeticCommitter<E>>(
//     cs: &mut CS,
//     path_bit: &Boolean,
//     current: &Num<E>,
//     path_witness: &Num<E>,
//     committer: &H
// ) -> Result<Num<E>, SynthesisError> {
//     // if path bit == 0 then left is current, right is witness
//     // if path bit == 1 then left is witness, right is current

//     let (left, right) = Num::conditionally_reverse(cs, &current, &path_witness, path_bit)?;

//     // let left = Num::conditionally_select(cs, path_bit, &path_witness, &current)?;
//     // let right = Num::conditionally_select(cs, path_bit, &current, &path_witness)?;

//     let mut committment = committer.commit(cs, &[left, right])?;

//     assert!(committment.len() >= 1);

//     let updated = committment.drain(0..1).next().expect("must containt at least one element");

//     Ok(updated)
// }

fn hash_to_node_with_round_function<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    path_bit: &Boolean,
    current: &Num<E>,
    path_witness: &Num<E>,
    round_function: &R,
) -> Result<Num<E>, SynthesisError> {
    // if path bit == 0 then left is current, right is witness
    // if path bit == 1 then left is witness, right is current

    let (left, right) = Num::conditionally_reverse(cs, &current, &path_witness, path_bit)?;

    // let left = Num::conditionally_select(cs, path_bit, &path_witness, &current)?;
    // let right = Num::conditionally_select(cs, path_bit, &current, &path_witness)?;
    let input = [left, right];
    use crate::glue::optimizable_queue::fixed_width_hash;
    let committment = fixed_width_hash(cs, &input, round_function)?;

    Ok(committment)
}

// #[track_caller]
// pub fn intersect_and_update_root<E: Engine, CS: ConstraintSystem<E>, H: CircuitArithmeticCommitter<E>>(
//     cs: &mut CS,
//     data_0: (&Num<E>, &MerklePathWitness<E>, &[Boolean]),
//     data_1: (&Num<E>, &MerklePathWitness<E>, &[Boolean]),
//     committer: &H,
// ) -> Result<Num<E>, SynthesisError> {
//     let (leaf_hash_0, path_witness_0, path_0) = data_0;
//     let (leaf_hash_1, path_witness_1, path_1) = data_1;
//     assert_eq!(path_0.len(), path_witness_0.witness().len());
//     assert_eq!(path_1.len(), path_witness_1.witness().len());
//     assert_eq!(path_0.len(), path_1.len());

//     let audit_path_0 = path_witness_0.witness();
//     let audit_path_1 = path_witness_1.witness();

//     // intersect first
//     let intersection_mask_bits = find_intersection_point(
//         cs,
//         path_0,
//         path_1,
//         audit_path_0,
//         audit_path_1,
//     )?;

//     let mut current_0 = leaf_hash_0.clone();
//     let mut current_1 = leaf_hash_1.clone();

//     // Ascend the merkle tree authentication path
//     for (i, ((path_bit_0, path_bit_1), intersection_bit)) in path_0.iter()
//         .zip(path_1.iter())
//         .zip(intersection_mask_bits.into_iter())
//         .enumerate()
//     {
//         let original_path_element_0 = audit_path_0[i].clone();
//         let original_path_element_1 = audit_path_1[i].clone();

//         // Now the most fancy part is to determine when to use path element form witness,
//         // or recalculated element from another subtree

//         // If we are on intersection place take a current hash from another branch instead of path element
//         let selected_path_element_0 = Num::conditionally_select(
//             cs,
//             &intersection_bit,
//             &current_1,
//             &original_path_element_0,
//         )?;

//         let selected_path_element_1 = Num::conditionally_select(
//             cs,
//             &intersection_bit,
//             &current_0,
//             &original_path_element_1,
//         )?;

//         // do the actual hashing
//         current_0 = hash_to_node(cs, path_bit_0, &current_0, &selected_path_element_0, committer)?;
//         current_1 = hash_to_node(cs, path_bit_1, &current_1, &selected_path_element_1, committer)?;
//     }

//     let is_equal = Num::equals(cs, &current_0, &current_1)?;

//     Boolean::enforce_equal(cs, &is_equal, &Boolean::constant(true))?;

//     Ok(current_0)
// }

// returns a bit vector with ones up to the first point of divergence
fn find_common_prefix<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &[Boolean],
    b: &[Boolean],
) -> Result<Vec<Boolean>, SynthesisError> {
    assert_eq!(a.len(), b.len());

    // initiall divergence did NOT happen yet
    let mut no_divergence_bool = Boolean::Constant(true);

    let mut mask_bools = vec![];

    for (_i, (a_bit, b_bit)) in a.iter().zip(b.iter()).enumerate() {
        // on common prefix mean a == b AND no divergence_bit

        // a == b -> NOT (a XOR b)

        let a_is_equal_to_b = Boolean::xor(cs, &a_bit, &b_bit)?.not();

        let mask_bool = Boolean::and(cs, &a_is_equal_to_b, &no_divergence_bool)?;

        // is no_divergence_bool == true: mask_bool = a == b
        // else: mask_bool == false
        // -->
        // if mask_bool == false: divergence = divergence AND mask_bool

        no_divergence_bool = Boolean::and(cs, &no_divergence_bool, &mask_bool)?;

        mask_bools.push(no_divergence_bool.clone());
    }

    Ok(mask_bools)
}

#[track_caller]
fn find_intersection_point<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    path_0: &[Boolean],
    path_1: &[Boolean],
    audit_path_0: &[Num<E>],
    audit_path_1: &[Num<E>],
) -> Result<Vec<Boolean>, SynthesisError> {
    assert_eq!(path_0.len(), path_1.len());
    assert_eq!(path_0.len(), audit_path_0.len());
    assert_eq!(path_1.len(), audit_path_1.len());

    // Intersection point is the only element required in outside scope
    let mut intersection_point_lc = LinearCombination::<E>::zero();

    // paths are usually from the bottom (LE), so we reverse
    let mut path_0_from_root = path_0.to_vec();
    path_0_from_root.reverse();

    let mut path_1_from_root = path_1.to_vec();
    path_1_from_root.reverse();

    let common_prefix = find_common_prefix(cs, &path_0_from_root, &path_1_from_root)?;

    // common prefix is reversed because it's enumerated from the root, while
    // audit path is from the leafs
    let mut common_prefix_reversed = common_prefix.clone();
    common_prefix_reversed.reverse();

    assert_eq!(audit_path_0.len(), common_prefix_reversed.len());

    // Common prefix is found, not we enforce equality of
    // audit path elements on a common prefix
    for (i, common_prefix_bit) in common_prefix_reversed.into_iter().enumerate() {
        let path_element_0 = &audit_path_0[i];
        let path_element_1 = &audit_path_1[i];

        let paths_are_equal = Num::equals(cs, path_element_0, path_element_1)?;

        // if bitmask == 1 then paths_are_equal == 1
        // else if bitmask == 0 then path_are_equal can be any,
        // so the only forbidden combination is bitmask = 1, paths_are_equal == 0
        let not_valid = Boolean::and(cs, &common_prefix_bit, &paths_are_equal.not())?;

        Boolean::enforce_equal(cs, &not_valid, &Boolean::constant(false))?;
    }

    // Now we have to find a "point of intersection"
    // Good for us it's just common prefix interpreted as binary number + 1
    // and bit decomposed

    let mut coeff = E::Fr::one();
    for bit in common_prefix.into_iter() {
        intersection_point_lc.add_assign_boolean_with_coeff(&bit, coeff);
        coeff.double();
    }

    // and add one
    intersection_point_lc.add_assign_constant(E::Fr::one());

    let as_num = intersection_point_lc.into_allocated_num(cs)?;

    let path_length_limit = path_0.len();
    let bit_limit = path_length_limit + 1;

    let mut decomposition = as_num.into_bits_le(cs, Some(bit_limit))?;
    decomposition.truncate(path_length_limit);
    // reverse cause bits here are counted from root, and later we need from the leaf
    decomposition.reverse();

    Ok(decomposition)
}
