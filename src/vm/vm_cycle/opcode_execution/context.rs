use super::*;
use crate::vm::primitives::register_view::*;

pub(crate) fn apply<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    _opcode_carry_parts: &OpcodeCarryParts<E>,
    _global_context: &GlobalContext<E>,
    optimizer: &mut OptimizationContext<E>,
    _round_function: &R,
    _witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<OpcodePartialApplicationResult<E, PropsMarker>, SynthesisError> {
    let n = cs.get_current_aux_gate_number();

    let retrieve_this_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::This,
    );
    let retrieve_caller_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::Caller,
    );
    let retrieve_code_address_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::CodeAddress,
    );
    let retrieve_meta_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::Meta,
    );
    let retrieve_ergs_left_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::ErgsLeft,
    );
    let retrieve_sp_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::Sp,
    );
    let get_context_u128_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::GetContextU128,
    );
    // attempt to execute in non-kernel mode for this opcode would be caught before
    let set_context_u128_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::SetContextU128,
    );
    let set_pubdata_ergs_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::SetErgsPerPubdataByte,
    );
    let increment_tx_num_opcode = zkevm_opcode_defs::Opcode::Context(
        zkevm_opcode_defs::definitions::context::ContextOpcode::IncrementTxNumber,
    );

    let should_apply = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_opcode(retrieve_this_opcode)
    };
    let marker = CtxMarker::from(retrieve_this_opcode);

    let is_retrieve_this = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(retrieve_this_opcode)
    };
    let is_retrieve_caller = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(retrieve_caller_opcode)
    };
    let is_retrieve_code_address = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(retrieve_code_address_opcode)
    };
    let is_retrieve_meta = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(retrieve_meta_opcode)
    };
    let is_retrieve_ergs_left = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(retrieve_ergs_left_opcode)
    };
    let is_retrieve_sp = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(retrieve_sp_opcode)
    };
    let is_get_context_u128 = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(get_context_u128_opcode)
    };
    let is_set_context_u128 = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(set_context_u128_opcode)
    };
    let is_set_pubdata_ergs = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(set_pubdata_ergs_opcode)
    };
    let is_inc_tx_num = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(increment_tx_num_opcode)
    };

    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing CONTEXT");
        if is_retrieve_this.get_value().unwrap_or(false) {
            println!("This");
        }
        if is_retrieve_caller.get_value().unwrap_or(false) {
            println!("msg.sender");
        }
        if is_retrieve_code_address.get_value().unwrap_or(false) {
            println!("Code address");
        }
        if is_retrieve_meta.get_value().unwrap_or(false) {
            println!("Meta");
        }
        if is_retrieve_ergs_left.get_value().unwrap_or(false) {
            println!("Ergs left");
        }
        if is_retrieve_sp.get_value().unwrap_or(false) {
            println!("SP");
        }
        if is_get_context_u128.get_value().unwrap_or(false) {
            println!("Get context u128");
        }
        if is_set_context_u128.get_value().unwrap_or(false) {
            println!("Set context u128");
        }
        if is_set_pubdata_ergs.get_value().unwrap_or(false) {
            println!("Set pubdata ergs");
        }
        if is_inc_tx_num.get_value().unwrap_or(false) {
            println!("Increment tx number");
        }
    }

    let write_to_context = smart_and(cs, &[should_apply, is_set_context_u128])?;
    let set_pubdata_ergs = smart_and(cs, &[should_apply, is_set_pubdata_ergs])?;
    let increment_tx_counter = smart_and(cs, &[should_apply, is_inc_tx_num])?;
    let write_to_dst0 = smart_and(
        cs,
        &[
            should_apply,
            is_set_context_u128.not(),
            is_inc_tx_num.not(),
            is_set_pubdata_ergs.not(),
        ],
    )?;

    let context_u128_as_num = {
        let shifts = compute_shifts::<E::Fr>();

        let mut shift_idx = 0;
        let mut lc = LinearCombination::zero();

        lc.add_assign_number_with_coeff(
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .context_u128_value_composite[0]
                .inner,
            shifts[shift_idx],
        );
        shift_idx += 64;
        lc.add_assign_number_with_coeff(
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .context_u128_value_composite[1]
                .inner,
            shifts[shift_idx],
        );
        shift_idx += 64;
        assert!(shift_idx <= E::Fr::CAPACITY as usize);

        lc.into_num(cs)?
    };

    let potentially_new_ergs_for_pubdata = common_opcode_state.src0_view.u32x8_view.unwrap()[0];

    let mut chosen = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .this
        .inner
        .clone();
    for (flag, value) in [
        (
            &is_retrieve_caller,
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .caller
                .inner,
        ),
        (
            &is_retrieve_code_address,
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .code_address
                .inner,
        ),
        (
            &is_retrieve_ergs_left,
            &common_opcode_state.preliminary_ergs_left.inner,
        ),
        (
            &is_retrieve_sp,
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .sp
                .inner,
        ),
        (&is_get_context_u128, &context_u128_as_num),
    ]
    .iter()
    {
        chosen = Num::conditionally_select(cs, flag, value, &chosen)?;
    }
    // now we need to convert non-aligned (but one that still fits into field element) value into [128-bit; 2]
    let register1 =
        optimizer.append_num_to_register_convesion(cs, &chosen, should_apply, marker)?;
    // form meta register
    let register2 = {
        let shifts = compute_shifts::<E::Fr>();

        let mut shift_idx = 0;
        let mut lc = LinearCombination::zero();
        // erge per pubdata
        lc.add_assign_number_with_coeff(
            &current_state.ergs_per_pubdata_byte.inner,
            shifts[shift_idx],
        );
        shift_idx += 32;
        shift_idx += 32; // skip upper bits
                         // heap sizes
        lc.add_assign_number_with_coeff(
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .heap_upper_bound
                .inner,
            shifts[shift_idx],
        );
        shift_idx += 32;
        lc.add_assign_number_with_coeff(
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .aux_heap_upper_bound
                .inner,
            shifts[shift_idx],
        );
        shift_idx += 32;
        assert!(shift_idx <= 128);
        assert!(shift_idx <= E::Fr::CAPACITY as usize);
        let low_word = lc.into_num(cs)?;
        let low_word = UInt128::from_num_unchecked(low_word);

        let mut shift_idx = 0;
        let mut lc = LinearCombination::zero();
        shift_idx += 64; // skip one u64 word
        shift_idx += 32; // use upper bits
        lc.add_assign_number_with_coeff(
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .this_shard_id
                .inner,
            shifts[shift_idx],
        );
        shift_idx += 8;
        lc.add_assign_number_with_coeff(
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .caller_shard_id
                .inner,
            shifts[shift_idx],
        );
        shift_idx += 8;
        lc.add_assign_number_with_coeff(
            &current_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .code_shard_id
                .inner,
            shifts[shift_idx],
        );
        shift_idx += 8;
        assert!(shift_idx <= 128);
        assert!(shift_idx <= E::Fr::CAPACITY as usize);
        let high_word = lc.into_num(cs)?;
        let high_word = UInt128::<E>::from_num_unchecked(high_word);

        Register {
            inner: [low_word, high_word],
            is_ptr: Boolean::Constant(false),
        }
    };
    let register = Register::conditionally_select(cs, &is_retrieve_meta, &register2, &register1)?;

    let context_composite_u128_to_set = [
        common_opcode_state.src0_view.u64x4_view.as_ref().unwrap()[0],
        common_opcode_state.src0_view.u64x4_view.as_ref().unwrap()[1],
    ];

    let (incremented_tx_number, _of) = current_state.tx_number_in_block.increment_checked(cs)?;
    // can_not_be_false_if_flagged(cs, &of.not(), &increment_tx_counter)?;

    let mut result = OpcodePartialApplicationResult::default();
    result.marker = PropsMarker::Normal(retrieve_this_opcode);
    result.applies = should_apply;
    result.context_u128_new_value = Some((write_to_context, context_composite_u128_to_set));
    result.new_ergs_per_pubdata_byte = Some((set_pubdata_ergs, potentially_new_ergs_for_pubdata));
    result.new_tx_number_in_block = Some((increment_tx_counter, incremented_tx_number));

    // this opcode updates dst0
    result.dst0_value = Some((write_to_dst0, register));

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!(
        "{} gates used for opcode {:?}",
        gates_used, retrieve_this_opcode
    );
    // dbg!(_message);

    Ok(result)
}
