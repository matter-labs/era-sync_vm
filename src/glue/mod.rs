use super::*;

pub mod binary_hashes;

pub mod aux_byte_markers;
pub mod code_unpacker_sha256;
pub mod demux_log_queue;
pub mod ecrecover_circuit;
pub mod keccak256_round_function_circuit;
pub mod log_sorter;
pub mod memory_queries_validity;
pub mod merkleize_l1_messages;
pub mod optimizable_queue;
pub mod pubdata_hasher;
pub mod ram_permutation;
pub mod sha256_round_function_circuit;
pub mod sort_decommittment_requests;
pub mod sponge_like_optimizable_queue;
pub mod storage_application;
pub mod storage_validity_by_grand_product;
pub mod traits;

use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::SynthesisError;
use crate::circuit_structures::bytes32::*;
use crate::circuit_structures::traits::*;
use crate::circuit_structures::utils::*;
use crate::circuit_structures::*;
use crate::data_structures::markers::*;
use crate::data_structures::markers::*;
use crate::derivative::*;
use crate::ff::*;
use crate::pairing::*;
use crate::traits::*;
use crate::utils::*;
use crate::vm::optimizer::*;
use crate::vm::partitioner::{smart_and, smart_or};
use crate::vm::primitives::uint256::*;
use crate::vm::primitives::utils::*;
use crate::vm::primitives::*;
use crate::vm::structural_eq::*;
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::bigint::bigint::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::byte::*;
use franklin_crypto::plonk::circuit::custom_rescue_gate::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::permutation_network::*;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::plonk::circuit::Assignment;
use franklin_crypto::rescue::*;
use num_bigint::BigUint;

#[cfg(test)]
use crate::testing::*;

use super::*;

/// check that a == b and a > b by performing a long subtraction b - a with borrow
#[track_caller]
pub fn long_comparison<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &[Num<E>],
    b: &[Num<E>],
    width_data: &[Vec<usize>],
) -> Result<(Boolean, Boolean), SynthesisError> {
    let mut num_items = 0;
    for w in width_data.iter() {
        num_items += w.len();
    }
    assert_eq!(a.len(), num_items);
    assert_eq!(a.len(), num_items);

    let mut a = a.iter();
    let mut b = b.iter();

    let shifts = compute_shifts::<E::Fr>();

    let mut a_packed_els = vec![];
    let mut b_packed_els = vec![];
    let mut final_width_data = vec![];

    for chunk in width_data.iter() {
        let mut a_packed = LinearCombination::zero();
        let mut b_packed = LinearCombination::zero();
        let mut full_width = 0;
        for width in chunk.iter() {
            let a_item = (&mut a).next().expect("is some");
            a_packed.add_assign_number_with_coeff(a_item, shifts[full_width]);

            let b_item = (&mut b).next().expect("is some");
            b_packed.add_assign_number_with_coeff(b_item, shifts[full_width]);
            full_width += width;
        }
        assert!(full_width <= E::Fr::CAPACITY as usize);
        let a_packed = a_packed.into_num(cs)?;
        let b_packed = b_packed.into_num(cs)?;

        a_packed_els.push(a_packed);
        b_packed_els.push(b_packed);
        final_width_data.push(full_width);
    }

    assert!(a.next().is_none());
    assert!(b.next().is_none());

    prepacked_long_comparison(cs, &a_packed_els, &b_packed_els, &final_width_data)
}

/// Check that a == b and a > b by performing a long subtraction b - a with borrow.
/// Both a and b are considered as least significant word first
#[track_caller]
pub fn prepacked_long_comparison<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &[Num<E>],
    b: &[Num<E>],
    width_data: &[usize],
) -> Result<(Boolean, Boolean), SynthesisError> {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), width_data.len());
    for w in width_data {
        assert!(*w <= E::Fr::CAPACITY as usize);
    }
    let shifts = compute_shifts::<E::Fr>();

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut previous_borrow = Boolean::constant(false);
    let mut limbs_are_equal = vec![];

    for ((a, b), width) in a.iter().zip(b.iter()).zip(width_data.iter()) {
        let (result_witness, borrow_witness) =
            match (a.get_value(), b.get_value(), previous_borrow.get_value()) {
                (Some(a), Some(b), Some(previous_borrow_value)) => {
                    use num_integer::Integer;
                    use num_traits::Zero;

                    let a = fe_to_biguint(&a);
                    let b = fe_to_biguint(&b);
                    let borrow_guard = BigUint::from(1u64) << width;

                    let tmp =
                        borrow_guard.clone() + b - a - BigUint::from(previous_borrow_value as u64);
                    let (q, r) = tmp.div_rem(&borrow_guard);

                    let borrow = q.is_zero();
                    let wit = biguint_to_fe(r);

                    (Some(wit), Some(borrow))
                }
                _ => (None, None),
            };

        let borrow = Boolean::alloc(cs, borrow_witness)?;
        let intermediate_result = Num::alloc(cs, result_witness)?;
        constraint_bit_length(cs, &intermediate_result, *width)?;

        let intermediate_is_zero = intermediate_result.is_zero(cs)?;
        limbs_are_equal.push(intermediate_is_zero);

        // b - a - previous_borrow + 2^X * borrow = intermediate

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&b, E::Fr::one());
        lc.add_assign_number_with_coeff(&a, minus_one);
        lc.add_assign_boolean_with_coeff(&previous_borrow, minus_one);
        lc.add_assign_number_with_coeff(&intermediate_result, minus_one);
        lc.add_assign_boolean_with_coeff(&borrow, shifts[*width]);
        lc.enforce_zero(cs)?;

        previous_borrow = borrow;
    }

    let final_borrow = previous_borrow;
    let eq = smart_and(cs, &limbs_are_equal)?;

    Ok((eq, final_borrow))
}

impl<E: Engine> IntoBytesStrict<E> for UInt256<E> {
    fn into_le_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        self.into_le_bytes(cs)
    }

    fn into_be_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes_strict(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}

impl<E: Engine> IntoBytesStrict<E> for Boolean {
    fn into_le_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        self.into_le_bytes(cs)
    }

    fn into_be_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes_strict(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}

impl<E: Engine, W: WidthMarker> IntoBytesStrict<E> for SmallFixedWidthInteger<E, W> {
    fn into_le_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        self.into_le_bytes(cs)
    }

    fn into_be_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes_strict(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}

pub fn num_to_bits_strict<E: Engine, CS: ConstraintSystem<E>, const N: usize>(
    cs: &mut CS,
    el: &Num<E>,
) -> Result<[Boolean; N], SynthesisError> {
    let (high, low) = num_into_canonical_uint128_pair(cs, el)?;

    let low_bits = low.inner.get_variable().into_bits_le(cs, Some(128))?;
    let high_bits = high.inner.get_variable().into_bits_le(cs, Some(128))?;

    let mut result = [Boolean::constant(false); N];
    let mut it = result.iter_mut();
    for (b, low_bit) in (&mut it).zip(low_bits.into_iter()) {
        *b = low_bit;
    }
    for (b, high_bit) in it.zip(high_bits.into_iter()) {
        *b = high_bit;
    }

    Ok(result)
}

pub fn num_like_to_bits_strict<E: Engine, CS: ConstraintSystem<E>, const N: usize>(
    cs: &mut CS,
    el: &Num<E>,
    known_bit_limit: usize,
) -> Result<[Boolean; N], SynthesisError> {
    assert!(known_bit_limit < E::Fr::NUM_BITS as usize);
    assert!(known_bit_limit <= N);

    let bits = el.get_variable().into_bits_le(cs, Some(known_bit_limit))?;

    let mut result = [Boolean::constant(false); N];
    let mut it = result.iter_mut();
    for (b, bit) in (&mut it).zip(bits.into_iter()) {
        *b = bit;
    }

    Ok(result)
}
