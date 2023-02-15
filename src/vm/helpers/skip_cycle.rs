use super::*;

pub fn should_skip_cycle<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    any_pending: Boolean,
    execution_has_ended: Boolean,
) -> Result<Boolean, SynthesisError> {
    smart_or(cs, &[any_pending, execution_has_ended])
}

pub fn mask_into_nop<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    should_mask: &Boolean,
    opcode: UInt64<E>,
) -> Result<UInt64<E>, SynthesisError> {
    use zkevm_opcode_defs::decoding::*;
    let nop_encoding = EncodingModeProduction::nop_encoding();
    let constant = nop_encoding;
    let nop_opcode = UInt64::from_uint(constant);

    UInt64::conditionally_select(cs, should_mask, &nop_opcode, &opcode)
}

pub fn mask_into_panic<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    should_mask: &Boolean,
    opcode: UInt64<E>,
) -> Result<UInt64<E>, SynthesisError> {
    use zkevm_opcode_defs::decoding::*;
    let panic_encoding = EncodingModeProduction::exception_revert_encoding();
    let constant = panic_encoding;
    let panic_opcode = UInt64::from_uint(constant);

    UInt64::conditionally_select(cs, should_mask, &panic_opcode, &opcode)
}

pub const SUB_PC_BITS: usize = 2;
pub const SUB_PC_MASK: u16 = (1u16 << SUB_PC_BITS) - 1;

pub fn split_pc<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    pc: UInt16<E>,
) -> Result<(UInt16<E>, Num<E>), SynthesisError> {
    let (super_pc, sub_pc) = match pc.get_value() {
        Some(pc) => (Some(pc >> 2), Some(u16_to_fe::<E::Fr>(pc & SUB_PC_MASK))),
        _ => (None, None),
    };

    let super_pc = UInt16::allocate(cs, super_pc)?;
    let sub_pc = Num::alloc(cs, sub_pc)?;
    use crate::precompiles::utils::table_width_3_lookup;
    let sub_pc_sread_result = table_width_3_lookup(cs, VM_SUBPC_TO_BITMASK_TABLE_NAME, &[sub_pc])?;
    let subpc_spread = sub_pc_sread_result[0];

    Ok((super_pc, subpc_spread))
}

pub fn should_read_memory<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    did_call_or_ret_recently: Boolean,
    super_pc: UInt16<E>,
    previous_super_pc: UInt16<E>,
) -> Result<Boolean, SynthesisError> {
    let super_pc_are_equal = UInt16::equals(cs, &super_pc, &previous_super_pc)?;

    smart_or(cs, &[did_call_or_ret_recently, super_pc_are_equal.not()])
}
