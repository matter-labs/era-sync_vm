use super::super::helpers::opcode::*;
use super::*;

use zkevm_opcode_defs::{
    OPCODE_INPUT_VARIANT_FLAGS, OPCODE_OUTPUT_VARIANT_FLAGS, OPCODE_TYPE_BITS, REGISTERS_COUNT,
};

pub const NUM_SRC_REGISTERS: usize = 2;
pub const NUM_DST_REGISTERS: usize = 2;
pub const REGISTER_ENCODING_BITS: usize = 4;

use super::opcode_bitmask::OpcodeBitmask;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct OpcodeFinalDecoding<E: Engine> {
    pub properties_bits: OpcodeBitmask<E>,
    pub src_regs_selectors: [[Boolean; REGISTERS_COUNT]; NUM_SRC_REGISTERS],
    pub dst_regs_selectors: [[Boolean; REGISTERS_COUNT]; NUM_DST_REGISTERS],
    pub imm0: UInt16<E>,
    pub imm1: UInt16<E>,
}

/// we assume that
/// - we did read the opcode either from memory, or have skipped opcode, or something else
/// - if we should have skipped cycle then we did it already
/// Now we need to decide either to mask into exception or into NOP, or execute
pub fn perform_initial_decoding<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    raw_opcode: UInt64<E>,
    encoded_flags: Num<E>,
    is_kernel_mode: Boolean,
    is_static_context: Boolean,
    callstack_is_full: Boolean,
    ergs_left: UInt32<E>,
    did_skip_cycle: Boolean,
    optimizer: &mut OptimizationContext<E>,
) -> Result<(OpcodeFinalDecoding<E>, UInt32<E>), SynthesisError> {
    // decode and resolve condition immediatelly
    // If we will later on mask into PANIC then we will just ignore resolved condition
    let initial_decoding = partially_decode_from_uint64_and_resolve_condition(
        cs,
        raw_opcode,
        encoded_flags,
        optimizer,
    )?;
    let (opcode_boolean_spread_data, aux_bools) =
        split_out_aux_bits(cs, initial_decoding.opcode_boolean_spread_data, optimizer)?;
    let condition_if_not_masked_later = initial_decoding.condition;

    // resolve fast exceptions
    // - out of ergs
    // - kernel mode
    // - writes in static context
    // - callstack is full

    // set ergs cost to 0 if we are skipping cycle
    let masked_ergs_cost = UInt32::from_num_unchecked(initial_decoding.ergs_cost.inner)
        .mask(cs, &did_skip_cycle.not())?;
    if crate::VERBOSE_CIRCUITS {
        println!(
            "Have {} ergs left, opcode uses {:?} ergs",
            ergs_left.get_value().unwrap(),
            masked_ergs_cost.get_value()
        );
    }
    let (ergs_left, out_of_ergs_exception) =
        ergs_left.sub_using_delayed_bool_allocation(cs, &masked_ergs_cost, optimizer)?;
    let ergs_left = ergs_left.mask(cs, &out_of_ergs_exception.not())?; // it's 0 if mask is 0, otherwise initial value

    let requires_kernel_mode = aux_bools[zkevm_opcode_defs::KERNER_MODE_FLAG_IDX];
    let can_be_used_in_static_context =
        aux_bools[zkevm_opcode_defs::CAN_BE_USED_IN_STATIC_CONTEXT_FLAG_IDX];
    let explicit_panic = aux_bools[zkevm_opcode_defs::EXPLICIT_PANIC_FLAG_IDX];

    let kernel_mode_exception = smart_and(cs, &[requires_kernel_mode, is_kernel_mode.not()])?;
    let write_in_static_exception = smart_and(
        cs,
        &[is_static_context, can_be_used_in_static_context.not()],
    )?;

    let any_exception = smart_or(
        cs,
        &[
            explicit_panic,
            out_of_ergs_exception,
            kernel_mode_exception,
            write_in_static_exception,
            callstack_is_full,
        ],
    )?;
    if crate::VERBOSE_CIRCUITS && any_exception.get_value().unwrap_or(false) {
        println!("EXCEPTION HAPPENED");
        if explicit_panic.get_value().unwrap_or(false) {
            println!("Explicit panic")
        }
        if out_of_ergs_exception.get_value().unwrap_or(false) {
            println!("Out of ergs")
        }
        if kernel_mode_exception.get_value().unwrap_or(false) {
            println!("Requires kernel mode")
        }
        if write_in_static_exception.get_value().unwrap_or(false) {
            println!("Write in static context")
        }
        if callstack_is_full.get_value().unwrap_or(false) {
            println!("Callstack is full")
        }
    }
    // dbg!(any_exception.get_value());

    // if we do have an exception then we have mask properties into PANIC
    let mask_into_panic = any_exception;
    // dbg!(mask_into_panic.get_value());
    // let panic_encoding = *zkevm_opcode_defs::PANIC_ENCODING_U64;
    let panic_encoding = *zkevm_opcode_defs::PANIC_BITSPREAD_U64;
    // println!("PANIC mask encoding = 0x{:016x}", panic_encoding);
    // mask out aux bits (those are 0, but do it just in case)
    let panic_encoding = panic_encoding & OPCODE_PROPS_BITMASK_FOR_BITSPREAD_ENCODING;
    // println!("Panic properties bits without aux flags = 0b{:064b}", panic_encoding);
    let panic_encoding = u64_to_fe::<E::Fr>(panic_encoding);
    let opcode_boolean_spread_data = Num::conditionally_select(
        cs,
        &mask_into_panic,
        &Num::Constant(panic_encoding),
        &opcode_boolean_spread_data,
    )?;

    // then if we didn't mask into panic and condition was false then mask into NOP
    let mask_into_nop = smart_and(
        cs,
        &[mask_into_panic.not(), condition_if_not_masked_later.not()],
    )?;
    // dbg!(mask_into_nop.get_value());
    // let nop_encoding = *zkevm_opcode_defs::NOP_ENCODING_U64;
    let nop_encoding = *zkevm_opcode_defs::NOP_BITSPREAD_U64;
    // println!("NOP mask encoding = 0x{:016x}", nop_encoding);
    // mask out aux bits (those are 0, but do it just in case)
    let nop_encoding = nop_encoding & OPCODE_PROPS_BITMASK_FOR_BITSPREAD_ENCODING;
    // println!("NOP properties bits without aux flags = 0b{:064b}", nop_encoding);
    let nop_encoding = u64_to_fe::<E::Fr>(nop_encoding);
    let opcode_boolean_spread_data = Num::conditionally_select(
        cs,
        &mask_into_nop,
        &Num::Constant(nop_encoding),
        &opcode_boolean_spread_data,
    )?;

    // println!("Opcode properties bits after masking = 0b{:064b}", fe_to_u128(opcode_boolean_spread_data.get_value().unwrap()));

    let mask_any = smart_or(cs, &[mask_into_nop, mask_into_panic])?;

    // Ok, now just decompose spreads into bitmasks, and spread and decompose register indexes

    use super::opcode_bitmask::TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED;

    let all_opcodes_props_bits = spread_into_bits::<_, _, TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED>(
        cs,
        opcode_boolean_spread_data,
        optimizer,
    )?;

    let src_regs_encoding = Num::mask(
        cs,
        &initial_decoding.src_regs_encoding.inner,
        &mask_any.not(),
    )?;
    let dst_regs_encoding = Num::mask(
        cs,
        &initial_decoding.dst_regs_encoding.inner,
        &mask_any.not(),
    )?;

    let src_encoding_slices = split_some_into_fixed_number_of_limbs(
        some_fe_to_biguint(&src_regs_encoding.get_value()),
        REGISTER_ENCODING_BITS,
        NUM_SRC_REGISTERS,
    );

    let dst_encoding_slices = split_some_into_fixed_number_of_limbs(
        some_fe_to_biguint(&dst_regs_encoding.get_value()),
        REGISTER_ENCODING_BITS,
        NUM_SRC_REGISTERS,
    );

    // for every register we first need to spread integer index -> bitmask as integer, and then transform integer bitmask into individual bits

    let src0_idx_num = Num::alloc(cs, some_biguint_to_fe(&src_encoding_slices[0]))?;
    let num = register_index_into_bitspread(cs, src0_idx_num)?;
    let src0_bitspread = spread_into_bits::<_, _, REGISTERS_COUNT>(cs, num, optimizer)?;

    let src1_idx_num = Num::alloc(cs, some_biguint_to_fe(&src_encoding_slices[1]))?;
    let num = register_index_into_bitspread(cs, src1_idx_num)?;
    let src1_bitspread = spread_into_bits::<_, _, REGISTERS_COUNT>(cs, num, optimizer)?;

    let dst0_idx_num = Num::alloc(cs, some_biguint_to_fe(&dst_encoding_slices[0]))?;
    let num = register_index_into_bitspread(cs, dst0_idx_num)?;
    let dst0_bitspread = spread_into_bits::<_, _, REGISTERS_COUNT>(cs, num, optimizer)?;

    let dst1_idx_num = Num::alloc(cs, some_biguint_to_fe(&dst_encoding_slices[1]))?;
    let num = register_index_into_bitspread(cs, dst1_idx_num)?;
    let dst1_bitspread = spread_into_bits::<_, _, REGISTERS_COUNT>(cs, num, optimizer)?;

    // enforce that we indeed decomposed original encodings

    let shift_4 = E::Fr::from_str("16").unwrap();
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&src0_idx_num, E::Fr::one());
    lc.add_assign_number_with_coeff(&src1_idx_num, shift_4);
    lc.add_assign_number_with_coeff(&src_regs_encoding, minus_one);
    lc.enforce_zero(cs)?;

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&dst0_idx_num, E::Fr::one());
    lc.add_assign_number_with_coeff(&dst1_idx_num, shift_4);
    lc.add_assign_number_with_coeff(&dst_regs_encoding, minus_one);
    lc.enforce_zero(cs)?;

    let imm0 = initial_decoding.imm0;
    let imm1 = initial_decoding.imm1;

    // place everything into struct

    let opcode_props = OpcodeBitmask::from_full_mask(all_opcodes_props_bits);

    let new = OpcodeFinalDecoding {
        properties_bits: opcode_props,
        src_regs_selectors: [src0_bitspread, src1_bitspread],
        dst_regs_selectors: [dst0_bitspread, dst1_bitspread],
        imm0,
        imm1,
    };

    Ok((new, ergs_left))
}

pub fn spread_into_bits<E: Engine, CS: ConstraintSystem<E>, const LIMIT: usize>(
    cs: &mut CS,
    num: Num<E>,
    optimizer: &mut OptimizationContext<E>,
) -> Result<[Boolean; LIMIT], SynthesisError> {
    let witness = match num.get_value() {
        Some(value) => {
            let repr = value.into_repr();
            // this is MSB iterator
            let bit_iterator = BitIterator::new(&repr);

            let mut result = vec![];
            for el in bit_iterator {
                result.push(el);
            }
            // now it's LSB based
            result.reverse();

            Some(result)
        }
        None => None,
    };

    let mut result = [Boolean::constant(false); LIMIT];
    for (i, dst) in result.iter_mut().enumerate() {
        let wit = witness.as_ref().map(|el| el[i]);
        let boolean = optimizer.allocate_boolean(cs, wit)?;
        *dst = boolean
    }

    let mut offset = E::Fr::one();
    let mut lc = LinearCombination::zero();
    for bit in result.iter() {
        lc.add_assign_boolean_with_coeff(&bit, offset);
        offset.double();
    }
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    lc.add_assign_number_with_coeff(&num, minus_one);
    lc.enforce_zero(cs)?;

    Ok(result)
}

pub fn register_index_into_bitspread<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    reg_encoding: Num<E>,
) -> Result<Num<E>, SynthesisError> {
    use crate::precompiles::utils::table_width_3_lookup;

    let vals = table_width_3_lookup(cs, VM_NUM_TO_BITMASK_TABLE_NAME, &[reg_encoding])?;
    let bitspread = vals[0];

    Ok(bitspread)
}
