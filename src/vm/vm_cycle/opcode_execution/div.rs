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

    let opcode = zkevm_opcode_defs::Opcode::Div(zkevm_opcode_defs::DivOpcode);
    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing DIV");
    }
    let should_set_flags = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[SET_FLAGS_FLAG_IDX];
    let marker = CtxMarker::from(opcode);

    let src0_view = &common_opcode_state.src0_view;
    let src1_view = &common_opcode_state.src1_view;
    let src1 = &common_opcode_state.src1;

    let (quotient, remainder) =
        optimizer.add_div_relation(cs, src0_view, src1_view, should_apply, marker)?;
    let quotient: Register<E> = quotient.unwrap_as_register();
    // check if b == 0
    let divisor_is_zero = optimizer.add_zero_check(cs, src1, should_apply, marker)?;
    // check is remainder is 0
    let remainder_is_zero = optimizer.add_zero_check(
        cs,
        &remainder.clone().unwrap_as_register(),
        should_apply,
        marker,
    )?;

    // add check that remainder is smaller than divisor (if it is not zero)
    // divisor - remander + 2^256 * borrow = c =>
    // c + remainder = divisor + borrow * 2^256;
    let (_result, borrow) =
        optimizer.add_subtraction_relation(cs, src1_view, &remainder, should_apply, marker)?;

    // borrow == 0 enforces only that remainder <= divisor
    // however we want to enforce that remainder < divisor
    // to accomplish the latter we additionally check that remainder != divisor
    // the full condition therefore is the following:
    // divisor !=0 => borrow == 0 && remainder != divisor
    // which is equivalent to: divisor_is_zero || (borrow == 0 && remainder != divisor)

    let remainder = remainder.unwrap_as_register();
    let rem_eq_divisor = Register::equals(cs, src1, &remainder)?;
    let rem_is_less_than_divisor = Boolean::and(cs, &borrow.not(), &rem_eq_divisor.not())?;
    let first_check = Boolean::or(cs, &divisor_is_zero, &rem_is_less_than_divisor)?;
    Boolean::enforce_equal(cs, &first_check, &Boolean::constant(true))?;

    // if divisor (b) is zero, then we assume that quotient = 0
    // this is done for the vm to be fully deterministic
    // b is zero => q is zero is equal to ~ !(b is zero) || (q is zero)
    let quotient_is_zero = optimizer.add_zero_check(cs, &quotient, should_apply, marker)?;
    let second_check = Boolean::or(cs, &divisor_is_zero.not(), &quotient_is_zero)?;
    Boolean::enforce_equal(cs, &second_check, &Boolean::constant(true))?;

    let of_flag = divisor_is_zero;
    let eq_flag = smart_and(cs, &[divisor_is_zero.not(), quotient_is_zero])?;
    let gt_flag = smart_and(cs, &[divisor_is_zero.not(), remainder_is_zero])?;

    let new_flag_port = ArithmeticFlagsPort::<E> {
        overflow_or_less_than: of_flag,
        equal: eq_flag,
        greater_than: gt_flag,
        _marker: std::marker::PhantomData::<E>,
    };

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(opcode);
    opcode_partial_application.applies = should_apply;
    opcode_partial_application.dst0_value = Some((should_apply, quotient));
    opcode_partial_application.dst1_value = Some((should_apply, remainder));

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
