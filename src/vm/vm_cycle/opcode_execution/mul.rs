use super::*;
use crate::vm::ports::ArithmeticFlagsPort;
use crate::vm::primitives::register_view::*;

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

    let opcode = zkevm_opcode_defs::Opcode::Mul(zkevm_opcode_defs::MulOpcode);
    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing MUL");
    }
    let should_set_flags = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[SET_FLAGS_FLAG_IDX];
    let marker = CtxMarker::from(opcode);

    let src0_view = &common_opcode_state.src0_view;
    let src1_view = &common_opcode_state.src1_view;

    let (result_low, result_high) =
        optimizer.add_mul_relation(cs, src0_view, src1_view, should_apply, marker)?;
    let result_high = result_high.unwrap_as_register();
    let result_low = result_low.unwrap_as_register();
    let high_is_zero = optimizer.add_zero_check(cs, &result_high, should_apply, marker)?;
    let low_is_zero = optimizer.add_zero_check(cs, &result_low, should_apply, marker)?;

    let of = high_is_zero.not();
    let eq = low_is_zero;
    let gt = smart_and(cs, &[of.not(), eq.not()])?;

    let new_flag_port = ArithmeticFlagsPort::<E> {
        overflow_or_less_than: of,
        equal: eq,
        greater_than: gt,
        _marker: std::marker::PhantomData::<E>,
    };

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(opcode);
    opcode_partial_application.applies = should_apply;
    opcode_partial_application.dst0_value = Some((should_apply, result_low));
    opcode_partial_application.dst1_value = Some((should_apply, result_high));

    let set_flags_and_execute = smart_and(cs, &[should_apply, should_set_flags])?;
    opcode_partial_application
        .flags
        .push((set_flags_and_execute, new_flag_port));

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for opcode {:?}", gates_used, opcode);
    // dbg!(_message);

    Ok(opcode_partial_application)
}
