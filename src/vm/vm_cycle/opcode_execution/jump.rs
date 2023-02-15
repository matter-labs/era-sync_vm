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

    let opcode = zkevm_opcode_defs::Opcode::Jump(zkevm_opcode_defs::JumpOpcode);
    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing JUMP");
    }
    let _marker = CtxMarker::from(opcode);

    let shifts = compute_shifts::<E::Fr>();
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(
        &common_opcode_state.src0_view.u8x32_view.as_ref().unwrap()[0].inner,
        shifts[0],
    );
    lc.add_assign_number_with_coeff(
        &common_opcode_state.src0_view.u8x32_view.as_ref().unwrap()[1].inner,
        shifts[8],
    );
    let destination = UInt16::from_num_unchecked(lc.into_num(cs)?);

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(opcode);
    opcode_partial_application.applies = should_apply;
    opcode_partial_application.new_pc = Some(destination);

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for opcode {:?}", gates_used, opcode);
    // dbg!(_message);

    Ok(opcode_partial_application)
}
