use super::*;
use crate::vm::{ports::ArithmeticFlagsPort, primitives::register_view::Register};

pub(crate) fn apply<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    _current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    _opcode_carry_parts: &OpcodeCarryParts<E>,
    _global_context: &GlobalContext<E>,
    optimizer: &mut OptimizationContext<E>,
    _round_function: &R,
    _witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<OpcodePartialApplicationResult<E, PropsMarker>, SynthesisError> {
    let n = cs.get_current_aux_gate_number();

    let ptr_add_opcode = zkevm_opcode_defs::Opcode::Ptr(zkevm_opcode_defs::PtrOpcode::Add);
    let ptr_sub_opcode = zkevm_opcode_defs::Opcode::Ptr(zkevm_opcode_defs::PtrOpcode::Sub);
    let ptr_pack_opcode = zkevm_opcode_defs::Opcode::Ptr(zkevm_opcode_defs::PtrOpcode::Pack);
    let ptr_shrink_opcode = zkevm_opcode_defs::Opcode::Ptr(zkevm_opcode_defs::PtrOpcode::Shrink);

    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(ptr_add_opcode);
    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing PTR");
    }

    let ptr_add_variant = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(ptr_add_opcode);
    let ptr_sub_variant = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(ptr_sub_opcode);
    let ptr_pack_variant = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(ptr_pack_opcode);
    let ptr_shrink_variant = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(ptr_shrink_opcode);

    let _marker = CtxMarker::from(ptr_add_opcode);

    let src_0 = &common_opcode_state.src0_view;
    let src_1 = &common_opcode_state.src1_view;

    // pointer + non_pointer
    let is_valid_args = smart_and(cs, &[src_0.is_ptr, src_1.is_ptr.not()])?;

    // check that for ptr_add/sub we have small offset
    let src1_32_64_is_zero = src_1.u32x8_view.unwrap()[1].is_zero(cs)?;
    let src1_64_128_is_zero = src_1.u64x4_view.unwrap()[1].is_zero(cs)?;
    let src1_128_256_is_zero = src_1.u128x2_view.unwrap()[1].is_zero(cs)?;

    let offset_is_in_range = smart_and(
        cs,
        &[
            src1_32_64_is_zero,
            src1_64_128_is_zero,
            src1_128_256_is_zero,
        ],
    )?;

    let mut is_panic = smart_and(cs, &[should_apply, is_valid_args.not()])?;

    let src1_low_is_zero = src_1.u128x2_view.unwrap()[0].is_zero(cs)?;
    let panic_if_pack = smart_and(
        cs,
        &[should_apply, ptr_pack_variant, src1_low_is_zero.not()],
    )?;

    let (result_for_ptr_add, of) = src_0.u32x8_view.unwrap()[0].add_using_delayed_bool_allocation(
        cs,
        &src_1.u32x8_view.unwrap()[0],
        optimizer,
    )?;
    let panic_if_add_may_be = smart_or(cs, &[offset_is_in_range.not(), of])?;
    let panic_if_add = smart_and(cs, &[should_apply, ptr_add_variant, panic_if_add_may_be])?;

    let (result_for_ptr_sub, uf) = src_0.u32x8_view.unwrap()[0].sub_using_delayed_bool_allocation(
        cs,
        &src_1.u32x8_view.unwrap()[0],
        optimizer,
    )?;
    let panic_if_sub_may_be = smart_or(cs, &[offset_is_in_range.not(), uf])?;
    let panic_if_sub = smart_and(cs, &[should_apply, ptr_sub_variant, panic_if_sub_may_be])?;

    let (result_for_ptr_shrink, uf) = src_0.u32x8_view.unwrap()[3]
        .sub_using_delayed_bool_allocation(cs, &src_1.u32x8_view.unwrap()[0], optimizer)?;
    let panic_if_shrink = smart_and(cs, &[should_apply, ptr_shrink_variant, uf])?;

    is_panic = smart_or(
        cs,
        &[
            is_panic,
            panic_if_add,
            panic_if_sub,
            panic_if_pack,
            panic_if_shrink,
        ],
    )?;

    let update_reg = smart_and(cs, &[should_apply, is_panic.not()])?;

    // low 32 bits from addition or unchanged original values
    let low_u32_if_add_or_sub = UInt32::conditionally_select(
        cs,
        &ptr_add_variant,
        &result_for_ptr_add,
        &src_0.u32x8_view.unwrap()[0],
    )?;

    // low 32 bits from subtraction
    let low_u32_if_add_or_sub = UInt32::conditionally_select(
        cs,
        &ptr_sub_variant,
        &result_for_ptr_sub,
        &low_u32_if_add_or_sub,
    )?;

    // higher 32 bits if shrink
    let highest_u32_if_shrink = UInt32::conditionally_select(
        cs,
        &ptr_shrink_variant,
        &result_for_ptr_shrink,
        &src_0.u32x8_view.unwrap()[3], // otherwise keep src_0 bits 96..128
    )?;

    let shifts = compute_shifts::<E::Fr>();
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&low_u32_if_add_or_sub.inner, shifts[0]);
    lc.add_assign_number_with_coeff(&src_0.u32x8_view.unwrap()[1].inner, shifts[32]);
    lc.add_assign_number_with_coeff(&src_0.u32x8_view.unwrap()[2].inner, shifts[64]);
    lc.add_assign_number_with_coeff(&highest_u32_if_shrink.inner, shifts[96]);

    let low_u128_if_add_sub_or_shrink = UInt128::from_num_unchecked(lc.into_num(cs)?);
    let low_u128 = UInt128::conditionally_select(
        cs,
        &ptr_pack_variant,
        &src_0.u128x2_view.unwrap()[0], // if pack - take from src0
        &low_u128_if_add_sub_or_shrink, // otherwise use result of add/sub
    )?;

    let high_u128 = UInt128::conditionally_select(
        cs,
        &ptr_pack_variant,
        &src_1.u128x2_view.unwrap()[1], // if pack - take from src1
        &src_0.u128x2_view.unwrap()[1], // otherwise use whatever is at the top of src0
    )?;

    let result = Register {
        inner: [low_u128, high_u128],
        is_ptr: Boolean::constant(true),
    };

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(ptr_add_opcode);
    opcode_partial_application.applies = should_apply;
    opcode_partial_application.dst0_value = Some((update_reg, result)); // no divergences
    opcode_partial_application.pending_exception = Some(is_panic);

    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        if is_panic.get_value().unwrap_or(false) {
            println!("PTR instruction raises an exception");
        }
    }

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for opcode {:?}", gates_used, ptr_add_variant);
    // dbg!(_message);

    Ok(opcode_partial_application)
}
