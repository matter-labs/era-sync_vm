use super::*;
use crate::vm::ports::ArithmeticFlagsPort;

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

    let opcode = zkevm_opcode_defs::Opcode::Sub(zkevm_opcode_defs::SubOpcode::Sub);
    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing SUB");
    }
    let should_set_flags = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[SET_FLAGS_FLAG_IDX];
    let marker = CtxMarker::from(opcode);

    let src_0 = &common_opcode_state.src0_view;
    let src_1 = &common_opcode_state.src1_view;
    let (result, new_bf) =
        optimizer.add_subtraction_relation(cs, src_0, src_1, should_apply, marker)?;
    let eq = optimizer.add_zero_check(cs, &result, should_apply, marker)?;
    let gt = Boolean::and(cs, &new_bf.not(), &eq.not())?;

    let new_flag_port = ArithmeticFlagsPort::<E> {
        overflow_or_less_than: new_bf,
        equal: eq,
        greater_than: gt,
        _marker: std::marker::PhantomData::<E>,
    };

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(opcode);
    opcode_partial_application.applies = should_apply;
    opcode_partial_application.dst0_value = Some((should_apply, result));

    // let original_flags = common_opcode_state.current_flags;
    // let preserve_flags_and_execute = smart_and(cs, &[should_apply, should_set_flags.not()])?;
    // opcode_partial_application.flags.push((preserve_flags_and_execute, original_flags));

    // flags for a case if we do not set flags
    let set_flags_and_execute = smart_and(cs, &[should_apply, should_set_flags])?;
    opcode_partial_application
        .flags
        .push((set_flags_and_execute, new_flag_port));

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for opcode {:?}", gates_used, opcode);
    // dbg!(_message);

    Ok(opcode_partial_application)
}
