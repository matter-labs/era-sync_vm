use super::*;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::vm::ports::ArithmeticFlagsPort;
use crate::vm::primitives::register_view::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::LookupTableApplication;
use itertools::Itertools;
use std::sync::Arc;

pub(crate) fn apply_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    shift: &UInt8<E>,
    table: Arc<LookupTableApplication<E>>,
    _is_low: bool,
) -> Result<(UInt64<E>, UInt64<E>), SynthesisError> {
    assert!(!shift.inner.is_constant());
    let (chunk0, chunk1) = match shift.get_value() {
        None => (
            AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
            AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
        ),
        Some(val) => {
            let vals = table.query(&[u64_to_fe(val as u64)])?;
            (
                AllocatedNum::alloc(cs, || Ok(vals[0]))?,
                AllocatedNum::alloc(cs, || Ok(vals[1]))?,
            )
        }
    };

    let dummy = AllocatedNum::zero(cs);
    let gate_vars = [
        shift.inner.get_variable().get_variable(),
        chunk0.get_variable(),
        chunk1.get_variable(),
        dummy.get_variable(),
    ];

    cs.begin_gates_batch_for_step()?;
    cs.apply_single_lookup_gate(&gate_vars[..table.width()], table.clone())?;
    cs.allocate_variables_without_gate(&gate_vars, &[])?;
    cs.end_gates_batch_for_step()?;

    // cs.begin_gates_batch_for_step()?;
    // cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
    // cs.end_gates_batch_for_step()?;

    let res0 = Num::Variable(chunk0);
    let res1 = Num::Variable(chunk1);
    Ok((
        UInt64::from_num_unchecked(res0),
        UInt64::from_num_unchecked(res1),
    ))
}

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

    let rol_opcode =
        zkevm_opcode_defs::Opcode::Shift(zkevm_opcode_defs::definitions::shift::ShiftOpcode::Rol);
    let ror_opcode =
        zkevm_opcode_defs::Opcode::Shift(zkevm_opcode_defs::definitions::shift::ShiftOpcode::Ror);
    let shl_opcode =
        zkevm_opcode_defs::Opcode::Shift(zkevm_opcode_defs::definitions::shift::ShiftOpcode::Shl);
    let shr_opcode =
        zkevm_opcode_defs::Opcode::Shift(zkevm_opcode_defs::definitions::shift::ShiftOpcode::Shr);

    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(rol_opcode);
    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing SHIFT");
    }
    let should_set_flags = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[SET_FLAGS_FLAG_IDX];
    let marker = CtxMarker::from(rol_opcode);

    let is_rol = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(rol_opcode);
    let is_ror = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(ror_opcode);
    let _is_shl = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(shl_opcode);
    let is_shr = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(shr_opcode);

    let is_cyclic = Boolean::or(cs, &is_rol, &is_ror)?;
    let is_right = Boolean::or(cs, &is_ror, &is_shr)?;

    let reg = &common_opcode_state.src0_view;
    let shift = common_opcode_state.src1_view.u8x32_view.unwrap()[0].clone();

    let shift_low_table = cs.get_table(VM_SHIFT_TO_NUM_LOW_TABLE_NAME)?;
    let shift_high_table = cs.get_table(VM_SHIFT_TO_NUM_HIGH_TABLE_NAME)?;

    // cyclic right rotation x is the same as left cyclic rotation 256 - x
    let change_rot = is_ror;
    let shift_is_zero = shift.inner.is_zero(cs)?;
    let inverted_shift =
        UInt8::from_num_unchecked(Num::Constant(u64_to_fe(256)).sub(cs, &shift.inner)?);

    let change_flag = Boolean::and(cs, &change_rot, &shift_is_zero.not())?;
    let final_shift = UInt8::conditionally_select(cs, &change_flag, &inverted_shift, &shift)?;

    let (chunk0, chunk1) = apply_table(cs, &final_shift, shift_low_table, true)?;
    let (chunk2, chunk3) = apply_table(cs, &final_shift, shift_high_table, false)?;
    let full_shift = RegisterInputView {
        u8x32_view: None,
        lowest160: None,
        decomposed_lowest160: None,
        u64x4_view: Some([chunk0, chunk1, chunk2, chunk3]),
        u128x2_view: None,
        u32x8_view: None,
        is_ptr: Boolean::Constant(false),
    };

    // for right_shift : a = rshift_q, b = full_shift, remainder = rshift_r, high = 0, low = reg
    let is_right_shift = Boolean::and(cs, &is_right, &is_cyclic.not())?;
    let apply_right_shift = Boolean::and(cs, &should_apply, &is_right_shift)?;
    let (rshift_q, _rshift_r) =
        optimizer.add_div_relation(cs, &reg, &full_shift, apply_right_shift, marker)?;

    // for left_shift: a = reg, b = full_shuft, remainder = 0, high = lshift_high, low = lshift_low
    let next_marker = marker.advance();
    let apply_left_shift = Boolean::and(cs, &should_apply, &is_right_shift.not())?;
    let (lshift_low, lshift_high) =
        optimizer.add_mul_relation(cs, &reg, &full_shift, apply_left_shift, next_marker)?;
    let rshift_q = rshift_q.unwrap_as_register();
    let lshift_low = lshift_low.unwrap_as_register();
    let temp_result = Register::conditionally_select(cs, &is_right_shift, &rshift_q, &lshift_low)?;
    let overflow = lshift_high.unwrap_as_register();
    let mut final_result = Register::zero();

    let zipped_iter = (
        temp_result.inner.iter(),
        overflow.inner.iter(),
        final_result.inner.iter_mut(),
    );
    for (limb_in, of_in, limb_out) in itertools::multizip(zipped_iter) {
        let res = of_in
            .inner
            .mask_by_boolean_into_accumulator(cs, &is_cyclic, &limb_in.inner)?;
        *limb_out = UInt128::from_num_unchecked(res);
    }

    // Sets an eq flag if out1 is zero
    let res_is_zero = optimizer.add_zero_check(cs, &final_result, should_apply, marker)?;
    let new_flag_port = ArithmeticFlagsPort::<E> {
        overflow_or_less_than: Boolean::Constant(false),
        equal: res_is_zero,
        greater_than: Boolean::Constant(false),
        _marker: std::marker::PhantomData::<E>,
    };

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(rol_opcode);
    opcode_partial_application.applies = should_apply;
    opcode_partial_application.dst0_value = Some((should_apply, final_result));

    // let original_flags = common_opcode_state.current_flags;
    // let preserve_flags_and_execute = smart_and(cs, &[should_apply, should_set_flags.not()])?;
    // opcode_partial_application.flags.push((preserve_flags_and_execute, original_flags));

    // flags for a case if we do not set flags
    let set_flags_and_execute = smart_and(cs, &[should_apply, should_set_flags])?;
    opcode_partial_application
        .flags
        .push((set_flags_and_execute, new_flag_port));

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for opcode {:?}", gates_used, rol_opcode);
    // dbg!(_message);

    Ok(opcode_partial_application)
}
