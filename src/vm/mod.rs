use crate::bellman::SynthesisError;
use crate::circuit_structures::byte::*;
use crate::circuit_structures::utils::*;
use crate::data_structures::markers::*;
use crate::derivative::*;
use crate::ff::*;
use crate::pairing::*;
use crate::utils::*;
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::simple_term::*;
use franklin_crypto::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;
use franklin_crypto::plonk::circuit::Assignment;

use crate::circuit_structures::SmallFixedWidthInteger;
use crate::data_structures::markers::*;
use arrayvec::ArrayVec;
use franklin_crypto::plonk::circuit::bigint::bigint::*;
use franklin_crypto::plonk::circuit::bigint::*;
use franklin_crypto::plonk::circuit::rescue::PlonkCsSBox;
use num_bigint::BigUint;
use std::iter;

pub mod helpers;
pub mod optimizer;
pub mod primitives;
pub mod vm_cycle;
pub mod vm_state;

pub mod franklin_extension;
pub mod partitioner;
pub mod ports;
pub mod structural_eq;
pub mod tables;

use crate::circuit_structures::traits::*;
use franklin_extension::*;
use optimizer::*;
use partitioner::*;
use primitives::rescue_sponge::*;
use primitives::uint256::*;
use primitives::{UInt128, UInt16, UInt160, UInt32, UInt64, UInt8};
use rescue_poseidon::HashParams;
use structural_eq::*;

pub(crate) const VM_RANGE_CHECK_TABLE_WIDTH: usize = 16;
pub const VM_SHIFT_TO_NUM_LOW_TABLE_NAME: &'static str = "Shift (low) converter";
pub const VM_SHIFT_TO_NUM_HIGH_TABLE_NAME: &'static str = "Shift (high) converter";
pub const VM_BITWISE_LOGICAL_OPS_TABLE_NAME: &'static str = "Table for bitwise logical ops";
pub const VM_NUM_TO_BITMASK_TABLE_NAME: &'static str = "Num to bitmask converter table";
pub const VM_SUBPC_TO_BITMASK_TABLE_NAME: &'static str = "Sub_PC to bitmask conversion table";
pub const VM_OPCODE_DECODING_AND_PRICING_TABLE_NAME: &'static str =
    "Opcode decoding and pricing table";
pub const VM_CONDITIONAL_RESOLUTION_TABLE_NAME: &'static str = "Conditional resolution table";
pub const VM_BOOLEAN_BATCH_ALLOCATION_TABLE_NAME: &'static str = "Boolean batch allocation table";

pub const ROLLUP_SHARD_ID: u8 = 0;
pub const PORTER_SHARD_ID: u8 = 1;

pub fn check_if_bitmask_and_if_empty<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    mask: &[Boolean],
) -> Result<(Boolean, Boolean), SynthesisError> {
    // take a sum of bits in the mask, it should be 0 or 1
    let mut lc = LinearCombination::zero();
    for bit in mask.iter() {
        lc.add_assign_boolean_with_coeff(&bit, E::Fr::one());
    }

    let as_num = lc.into_num(cs)?;

    let empty = as_num.is_zero(cs)?;

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    // check that num is 0 or 1, so do a^2 - a = 0
    let value = as_num.get_variable().fma_with_coefficients(
        cs,
        (E::Fr::one(), as_num.get_variable()),
        (minus_one, as_num.get_variable()),
    )?;

    let is_boolean = value.is_zero(cs)?;

    Ok((is_boolean, empty))
}
