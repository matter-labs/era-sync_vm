use super::*;
// use crate::scheduler::linking::storage_log_demux::{LogDemultiplexorStructuredInput, LogDemultiplexorStructuredInputWitness, DemultiplexorStructuredLogicalOutputWitness};
use crate::glue::aux_byte_markers::*;
use crate::glue::optimizable_queue::commit_encodable_item;
use crate::glue::optimizable_queue::*;
use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::StorageLogQueue;
use crate::vm::check_if_bitmask_and_if_empty;
use crate::vm::optimizer::sponge_set::SpongeOptimizer;
use crate::vm::partitioner::smart_and;
use crate::vm::primitives::UInt16;
use crate::vm::structural_eq::CircuitSelectable;
use std::convert::TryInto;

pub mod input;

use self::input::*;

pub fn demultiplex_storage_logs_enty_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<LogDemuxerCircuitInstanceWitness<E>>,
    round_function: &R,
    limit: usize,
) -> Result<AllocatedNum<E>, SynthesisError> {
    use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
    use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    let columns3 = vec![
        PolyIdentifier::VariablesPolynomial(0),
        PolyIdentifier::VariablesPolynomial(1),
        PolyIdentifier::VariablesPolynomial(2),
    ];

    if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
        let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            BitwiseLogicTable::new(&name, 8),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(bitwise_logic_table)?;
    };

    inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let initial_queue_witness = project_ref!(witness, initial_queue_witness).cloned();

    let mut structured_input =
        LogDemuxerInputOutput::alloc_ignoring_outputs(cs, structured_input_witness.clone())?;

    let queue_states_from_fsm = [
        &structured_input.hidden_fsm_input.initial_log_queue_state,
        &structured_input.hidden_fsm_input.storage_access_queue_state,
        &structured_input.hidden_fsm_input.events_access_queue_state,
        &structured_input
            .hidden_fsm_input
            .l1messages_access_queue_state,
        &structured_input
            .hidden_fsm_input
            .keccak256_access_queue_state,
        &structured_input.hidden_fsm_input.sha256_access_queue_state,
        &structured_input
            .hidden_fsm_input
            .ecrecover_access_queue_state,
    ];

    let [initial_log_queue_state_from_fsm, storage_access_queue_state_from_fsm, events_access_queue_state_from_fsm, l1messages_access_queue_state_from_fsm, keccak256_access_queue_state_from_fsm, sha256_access_queue_state_from_fsm, ecrecover_access_queue_state_from_fsm] =
        queue_states_from_fsm.map(|el| {
            StorageLogQueue::from_raw_parts(cs, el.head_state, el.tail_state, el.num_items)
        });

    let initial_log_queue_state_from_fsm = initial_log_queue_state_from_fsm?;
    let storage_access_queue_state_from_fsm = storage_access_queue_state_from_fsm?;
    let events_access_queue_state_from_fsm = events_access_queue_state_from_fsm?;
    let l1messages_access_queue_state_from_fsm = l1messages_access_queue_state_from_fsm?;
    let keccak256_access_queue_state_from_fsm = keccak256_access_queue_state_from_fsm?;
    let sha256_access_queue_state_from_fsm = sha256_access_queue_state_from_fsm?;
    let ecrecover_access_queue_state_from_fsm = ecrecover_access_queue_state_from_fsm?;

    let initial_queue_from_passthrough = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .initial_log_queue_state
            .head_state,
        structured_input
            .observable_input
            .initial_log_queue_state
            .tail_state,
        structured_input
            .observable_input
            .initial_log_queue_state
            .num_items,
    )?;

    // passthrough must be trivial
    initial_queue_from_passthrough
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let mut initial_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &initial_queue_from_passthrough,
        &initial_log_queue_state_from_fsm,
    )?;

    // and assign witness
    if let Some(wit) = initial_queue_witness {
        initial_queue.witness = wit;
    }

    // for the rest it's just select between empty or from FSM

    let queue_states_from_fsm = [
        storage_access_queue_state_from_fsm,
        events_access_queue_state_from_fsm,
        l1messages_access_queue_state_from_fsm,
        keccak256_access_queue_state_from_fsm,
        sha256_access_queue_state_from_fsm,
        ecrecover_access_queue_state_from_fsm,
    ];

    let [storage_access_queue, events_access_queue, l1messages_access_queue, keccak256_access_queue, sha256_access_queue, ecrecover_access_queue] =
        queue_states_from_fsm.map(|el| {
            StorageLogQueue::conditionally_select(
                cs,
                &structured_input.start_flag,
                &StorageLogQueue::empty(),
                &el,
            )
        });

    let mut storage_access_queue = storage_access_queue?;
    let mut events_access_queue = events_access_queue?;
    let mut l1messages_access_queue = l1messages_access_queue?;
    let mut keccak256_access_queue = keccak256_access_queue?;
    let mut sha256_access_queue = sha256_access_queue?;
    let mut ecrecover_access_queue = ecrecover_access_queue?;

    let input_queues = [
        &mut storage_access_queue,
        &mut events_access_queue,
        &mut l1messages_access_queue,
        &mut keccak256_access_queue,
        &mut sha256_access_queue,
        &mut ecrecover_access_queue,
    ];

    demultiplex_storage_logs_inner_optimized(
        cs,
        &mut initial_queue,
        input_queues,
        round_function,
        limit,
    )?;

    // form the final state
    structured_input.observable_output = LogDemuxerOutputData::empty();

    let completed = initial_queue.is_empty(cs)?;
    structured_input.completion_flag = completed;

    structured_input.hidden_fsm_output.initial_log_queue_state = initial_queue.into_state();

    structured_input
        .hidden_fsm_output
        .storage_access_queue_state = storage_access_queue.into_state();

    structured_input.hidden_fsm_output.events_access_queue_state = events_access_queue.into_state();

    structured_input
        .hidden_fsm_output
        .l1messages_access_queue_state = l1messages_access_queue.into_state();

    structured_input
        .hidden_fsm_output
        .keccak256_access_queue_state = keccak256_access_queue.into_state();

    structured_input.hidden_fsm_output.sha256_access_queue_state = sha256_access_queue.into_state();

    structured_input
        .hidden_fsm_output
        .ecrecover_access_queue_state = ecrecover_access_queue.into_state();

    // copy into observable output
    use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;

    structured_input
        .observable_output
        .storage_access_queue_state = FixedWidthEncodingGenericQueueState::conditionally_select(
        cs,
        &completed,
        &structured_input
            .hidden_fsm_output
            .storage_access_queue_state,
        &structured_input
            .observable_output
            .storage_access_queue_state,
    )?;
    structured_input.observable_output.events_access_queue_state =
        FixedWidthEncodingGenericQueueState::conditionally_select(
            cs,
            &completed,
            &structured_input.hidden_fsm_output.events_access_queue_state,
            &structured_input.observable_output.events_access_queue_state,
        )?;
    structured_input
        .observable_output
        .l1messages_access_queue_state = FixedWidthEncodingGenericQueueState::conditionally_select(
        cs,
        &completed,
        &structured_input
            .hidden_fsm_output
            .l1messages_access_queue_state,
        &structured_input
            .observable_output
            .l1messages_access_queue_state,
    )?;
    structured_input
        .observable_output
        .keccak256_access_queue_state = FixedWidthEncodingGenericQueueState::conditionally_select(
        cs,
        &completed,
        &structured_input
            .hidden_fsm_output
            .keccak256_access_queue_state,
        &structured_input
            .observable_output
            .keccak256_access_queue_state,
    )?;
    structured_input.observable_output.sha256_access_queue_state =
        FixedWidthEncodingGenericQueueState::conditionally_select(
            cs,
            &completed,
            &structured_input.hidden_fsm_output.sha256_access_queue_state,
            &structured_input.observable_output.sha256_access_queue_state,
        )?;
    structured_input
        .observable_output
        .ecrecover_access_queue_state = FixedWidthEncodingGenericQueueState::conditionally_select(
        cs,
        &completed,
        &structured_input
            .hidden_fsm_output
            .ecrecover_access_queue_state,
        &structured_input
            .observable_output
            .ecrecover_access_queue_state,
    )?;

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = structured_input_witness {
            assert_eq!(circuit_result, passed_input);
        }
    }

    use crate::inputs::ClosedFormInputCompactForm;
    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    // dbg!(compact_form.create_witness());
    use crate::glue::optimizable_queue::commit_encodable_item;
    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();
    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;

    Ok(public_input)
}

pub const NUM_SEPARATE_QUEUES: usize = 6;

#[repr(u64)]
pub enum LogType {
    RollupStorage,
    PorterStorage,
    Events,
    L1Messages,
    KeccakCalls,
    Sha256Calls,
    ECRecoverCalls,
}

pub fn demultiplex_storage_logs_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    mut storage_log_queue: StorageLogQueue<E>,
    round_function: &R,
    limit: usize,
) -> Result<[StorageLogQueue<E>; NUM_SEPARATE_QUEUES], SynthesisError> {
    assert!(limit <= u32::MAX as usize);

    let mut optimizer = SpongeOptimizer::new(round_function.clone(), 3);

    let mut rollup_storage_queue = StorageLogQueue::empty();
    // let mut porter_storage_queue = StorageLogQueue::empty();
    let mut events_queue = StorageLogQueue::empty();
    let mut l1_messages_queue = StorageLogQueue::empty();
    let mut keccak_calls_queue = StorageLogQueue::empty();
    let mut sha256_calls_queue = StorageLogQueue::empty();
    let mut ecdsa_calls_queue = StorageLogQueue::empty();

    const SYSTEM_CONTRACTS_OFFSET_ADDRESS: u16 = 1 << 15;

    const KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: u16 = SYSTEM_CONTRACTS_OFFSET_ADDRESS + 0x10;
    const SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: u16 = 0x02; // as in Ethereum
    const ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS: u16 = 0x01; // as in Ethereum

    let keccak_precompile_address = UInt160::from_uint(u160::from_u64(
        KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS as u64,
    ));
    let sha256_precompile_address = UInt160::from_uint(u160::from_u64(
        SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS as u64,
    ));
    let ecrecover_precompile_address = UInt160::from_uint(u160::from_u64(
        ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS as u64,
    ));

    for _ in 0..limit {
        let execute = storage_log_queue.is_empty(cs)?.not();

        // let n = cs.get_current_step_number();
        let popped = storage_log_queue.pop_first(cs, &execute, round_function)?;
        // dbg!(cs.get_current_step_number() - n); // 291

        let is_storage_aux_byte =
            Num::equals(cs, &aux_byte_for_storage().inner, &popped.aux_byte.inner)?;
        let is_event_aux_byte =
            Num::equals(cs, &aux_byte_for_event().inner, &popped.aux_byte.inner)?;
        let is_l1_message_aux_byte =
            Num::equals(cs, &aux_byte_for_l1_message().inner, &popped.aux_byte.inner)?;
        let is_precompile_aux_byte = Num::equals(
            cs,
            &aux_byte_for_precompile_call().inner,
            &popped.aux_byte.inner,
        )?;

        let is_keccak_address = UInt160::equals(cs, &keccak_precompile_address, &popped.address)?;
        let is_sha256_address = UInt160::equals(cs, &sha256_precompile_address, &popped.address)?;
        let is_ecrecover_address =
            UInt160::equals(cs, &ecrecover_precompile_address, &popped.address)?;

        let is_rollup_shard = popped.shard_id.inner.is_zero(cs)?;

        let execute_rollup_storage =
            smart_and(cs, &[is_storage_aux_byte, is_rollup_shard, execute])?;
        let execute_porter_storage =
            smart_and(cs, &[is_storage_aux_byte, is_rollup_shard.not(), execute])?;
        Boolean::enforce_equal(cs, &execute_porter_storage, &Boolean::constant(false))?;
        let execute_event = smart_and(cs, &[is_event_aux_byte, execute])?;
        let execute_l1_message = smart_and(cs, &[is_l1_message_aux_byte, execute])?;
        let execute_keccak_call =
            smart_and(cs, &[is_precompile_aux_byte, is_keccak_address, execute])?;
        let execute_sha256_call =
            smart_and(cs, &[is_precompile_aux_byte, is_sha256_address, execute])?;
        let execute_ecrecover_call =
            smart_and(cs, &[is_precompile_aux_byte, is_ecrecover_address, execute])?;

        // let n = cs.get_current_step_number();
        rollup_storage_queue.push_with_optimizer(
            cs,
            LogType::RollupStorage as u64,
            &popped,
            &execute_rollup_storage,
            &mut optimizer,
        )?;
        // porter_storage_queue.push_with_optimizer(cs, LogType::PorterStorage as u64, &popped, &execute_porter_storage, &mut optimizer)?;
        events_queue.push_with_optimizer(
            cs,
            LogType::Events as u64,
            &popped,
            &execute_event,
            &mut optimizer,
        )?;
        l1_messages_queue.push_with_optimizer(
            cs,
            LogType::L1Messages as u64,
            &popped,
            &execute_l1_message,
            &mut optimizer,
        )?;
        keccak_calls_queue.push_with_optimizer(
            cs,
            LogType::KeccakCalls as u64,
            &popped,
            &execute_keccak_call,
            &mut optimizer,
        )?;
        sha256_calls_queue.push_with_optimizer(
            cs,
            LogType::Sha256Calls as u64,
            &popped,
            &execute_sha256_call,
            &mut optimizer,
        )?;
        ecdsa_calls_queue.push_with_optimizer(
            cs,
            LogType::ECRecoverCalls as u64,
            &popped,
            &execute_ecrecover_call,
            &mut optimizer,
        )?;
        // dbg!(cs.get_current_step_number() - n); // 96

        // let n = cs.get_current_step_number();
        optimizer.enforce(cs)?;
        // dbg!(cs.get_current_step_number() - n); // 338

        let expected_bitmask_bits = [
            is_storage_aux_byte,
            is_event_aux_byte,
            is_l1_message_aux_byte,
            is_precompile_aux_byte,
        ];

        let (is_bitmask, all_flags_are_false) =
            check_if_bitmask_and_if_empty(cs, &expected_bitmask_bits)?;
        can_not_be_false_if_flagged(cs, &is_bitmask, &Boolean::Constant(true))?;
        can_not_be_false_if_flagged(cs, &all_flags_are_false.not(), &execute)?;
    }

    storage_log_queue.enforce_to_be_empty(cs)?;

    let all_queues = [
        rollup_storage_queue,
        events_queue,
        l1_messages_queue,
        keccak_calls_queue,
        sha256_calls_queue,
        ecdsa_calls_queue,
    ];

    Ok(all_queues)
}

pub fn demultiplex_storage_logs_inner_optimized<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    storage_log_queue: &mut StorageLogQueue<E>,
    output_queues: [&mut StorageLogQueue<E>; NUM_SEPARATE_QUEUES],
    round_function: &R,
    limit: usize,
) -> Result<(), SynthesisError> {
    assert!(limit <= u32::MAX as usize);

    let mut optimizer = SpongeOptimizer::new(round_function.clone(), 3);

    let [rollup_storage_queue, events_queue, l1_messages_queue, keccak_calls_queue, sha256_calls_queue, ecdsa_calls_queue] =
        output_queues;

    const SYSTEM_CONTRACTS_OFFSET_ADDRESS: u16 = 1 << 15;

    const KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: u16 = SYSTEM_CONTRACTS_OFFSET_ADDRESS + 0x10;
    const SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: u16 = 0x02; // as in Ethereum
    const ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS: u16 = 0x01; // as in Ethereum

    let keccak_precompile_address = UInt160::from_uint(u160::from_u64(
        KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS as u64,
    ));
    let sha256_precompile_address = UInt160::from_uint(u160::from_u64(
        SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS as u64,
    ));
    let ecrecover_precompile_address = UInt160::from_uint(u160::from_u64(
        ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS as u64,
    ));

    let shifts = compute_shifts::<E::Fr>();

    let low_u64_divisor = BigUint::from(1u64) << 64u32;

    for _ in 0..limit {
        let execute = storage_log_queue.is_empty(cs)?.not();
        // here the trick is that we do not need to pop it in full because we only need to peek into
        // address + byte to determing demultiplexing. So we
        // - Get witness
        use crate::scheduler::queues::StorageLogRecordWitness;
        let wit = storage_log_queue
            .witness
            .wit
            .front()
            .map(|el| el.1.clone())
            .unwrap_or(StorageLogRecordWitness::empty());
        let wit = Some(wit);
        // - use knowledge about encoding format to compare only relevant parts

        // let n = cs.get_current_step_number();
        // IMPORTANT: this should be changed accordingly with encoding for StorageLogRecord
        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        let address = project_ref!(wit, address).cloned();
        let address = UInt160::alloc_from_witness(cs, address)?;
        lc.add_assign_number_with_coeff(&address.inner, shifts[shift]);
        shift += 160;
        let key_inner_0: Option<u64> = project_ref!(wit, key).map(|el| {
            use num_traits::ToPrimitive;

            (el % low_u64_divisor.clone()).to_u64().unwrap()
        });
        let key_inner_0 = UInt64::alloc_from_witness(cs, key_inner_0)?;
        lc.add_assign_number_with_coeff(&key_inner_0.inner, shifts[shift]);
        shift += 64;
        let shard_id = project_ref!(wit, shard_id).cloned();
        let shard_id = UInt8::alloc_from_witness(cs, shard_id)?;
        lc.add_assign_number_with_coeff(&shard_id.inner, shifts[shift]);
        shift += 8;
        let aux_byte = project_ref!(wit, aux_byte).cloned();
        let aux_byte = UInt8::alloc_from_witness(cs, aux_byte)?;
        lc.add_assign_number_with_coeff(&aux_byte.inner, shifts[shift]);
        shift += 8;
        let r_w_flag = project_ref!(wit, r_w_flag).cloned();
        let r_w_flag = Boolean::alloc_from_witness(cs, r_w_flag)?;
        lc.add_assign_boolean_with_coeff(&r_w_flag, shifts[shift]);
        shift += 1;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el0 = lc.into_num(cs)?;
        // and pop encoding only
        let popped = storage_log_queue.pop_first_encoding_only(cs, &execute, round_function)?;

        // enforce that relevant parts match
        Num::conditionally_enforce_equal(cs, &execute, &el0, &popped[0])?;

        // dbg!(cs.get_current_step_number() - n); // 291 -> 224

        let is_storage_aux_byte = Num::equals(cs, &aux_byte_for_storage().inner, &aux_byte.inner)?;
        let is_event_aux_byte = Num::equals(cs, &aux_byte_for_event().inner, &aux_byte.inner)?;
        let is_l1_message_aux_byte =
            Num::equals(cs, &aux_byte_for_l1_message().inner, &aux_byte.inner)?;
        let is_precompile_aux_byte =
            Num::equals(cs, &aux_byte_for_precompile_call().inner, &aux_byte.inner)?;

        let is_keccak_address = UInt160::equals(cs, &keccak_precompile_address, &address)?;
        let is_sha256_address = UInt160::equals(cs, &sha256_precompile_address, &address)?;
        let is_ecrecover_address = UInt160::equals(cs, &ecrecover_precompile_address, &address)?;

        let is_rollup_shard = shard_id.inner.is_zero(cs)?;

        let execute_rollup_storage =
            smart_and(cs, &[is_storage_aux_byte, is_rollup_shard, execute])?;
        let execute_porter_storage =
            smart_and(cs, &[is_storage_aux_byte, is_rollup_shard.not(), execute])?;
        Boolean::enforce_equal(cs, &execute_porter_storage, &Boolean::constant(false))?;
        let execute_event = smart_and(cs, &[is_event_aux_byte, execute])?;
        let execute_l1_message = smart_and(cs, &[is_l1_message_aux_byte, execute])?;
        let execute_keccak_call =
            smart_and(cs, &[is_precompile_aux_byte, is_keccak_address, execute])?;
        let execute_sha256_call =
            smart_and(cs, &[is_precompile_aux_byte, is_sha256_address, execute])?;
        let execute_ecrecover_call =
            smart_and(cs, &[is_precompile_aux_byte, is_ecrecover_address, execute])?;

        // let n = cs.get_current_step_number();
        rollup_storage_queue.push_raw_with_optimizer(
            cs,
            LogType::RollupStorage as u64,
            popped,
            wit.clone(),
            &execute_rollup_storage,
            &mut optimizer,
        )?;
        // porter_storage_queue.push_with_optimizer(cs, LogType::PorterStorage as u64, &popped, &execute_porter_storage, &mut optimizer)?;
        events_queue.push_raw_with_optimizer(
            cs,
            LogType::Events as u64,
            popped,
            wit.clone(),
            &execute_event,
            &mut optimizer,
        )?;
        l1_messages_queue.push_raw_with_optimizer(
            cs,
            LogType::L1Messages as u64,
            popped,
            wit.clone(),
            &execute_l1_message,
            &mut optimizer,
        )?;
        keccak_calls_queue.push_raw_with_optimizer(
            cs,
            LogType::KeccakCalls as u64,
            popped,
            wit.clone(),
            &execute_keccak_call,
            &mut optimizer,
        )?;
        sha256_calls_queue.push_raw_with_optimizer(
            cs,
            LogType::Sha256Calls as u64,
            popped,
            wit.clone(),
            &execute_sha256_call,
            &mut optimizer,
        )?;
        ecdsa_calls_queue.push_raw_with_optimizer(
            cs,
            LogType::ECRecoverCalls as u64,
            popped,
            wit.clone(),
            &execute_ecrecover_call,
            &mut optimizer,
        )?;
        // dbg!(cs.get_current_step_number() - n); // 96 -> 84

        // let n = cs.get_current_step_number();
        optimizer.enforce(cs)?;
        // dbg!(cs.get_current_step_number() - n); // 338 -> 301

        let expected_bitmask_bits = [
            is_storage_aux_byte,
            is_event_aux_byte,
            is_l1_message_aux_byte,
            is_precompile_aux_byte,
        ];

        let (is_bitmask, all_flags_are_false) =
            check_if_bitmask_and_if_empty(cs, &expected_bitmask_bits)?;
        can_not_be_false_if_flagged(cs, &is_bitmask, &Boolean::Constant(true))?;
        can_not_be_false_if_flagged(cs, &all_flags_are_false.not(), &execute)?;
    }

    Ok(())
}
