use super::*;

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
    _optimizer: &mut OptimizationContext<E>,
    _round_function: &R,
    _witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<OpcodePartialApplicationResult<E, PropsMarker>, SynthesisError> {
    let n = cs.get_current_aux_gate_number();

    let opcode = zkevm_opcode_defs::Opcode::Nop(zkevm_opcode_defs::NopOpcode);
    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing NOP");
    }
    let mut result = OpcodePartialApplicationResult::default();
    result.marker = PropsMarker::Normal(opcode);
    result.applies = should_apply;

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for opcode {:?}", gates_used, opcode);
    // dbg!(message);

    Ok(result)
}
