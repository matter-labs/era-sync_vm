use super::*;
use crate::glue::traits::*;
use crate::scheduler::queues::*;

pub mod input;

// This is a sorter of logs that are kind-of "pure", e.g. event emission or L2 -> L1 messages.
// Those logs do not affect a global state and may either be rolled back in full or not.
// We identify equality of logs using "timestamp" field that is a monotonic unique counter
// across the block

use crate::glue::log_sorter::input::*;

const NUM_PERMUTATION_ARG_CHALLENGES: usize = STORAGE_LOG_RECORD_ENCODING_LEN + 1;

pub fn sort_and_deduplicate_events_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<EventsDeduplicatorInstanceWitness<E>>,
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
    let intermediate_sorted_queue_witness =
        project_ref!(witness, intermediate_sorted_queue_witness).cloned();

    let mut structured_input = EventsDeduplicatorInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    )?;

    let unsorted_queue_from_passthrough = StorageLogQueue::from_raw_parts(
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

    // it must be trivial
    unsorted_queue_from_passthrough
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let unsorted_queue_from_fsm = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .initial_unsorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .initial_unsorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .initial_unsorted_queue_state
            .num_items,
    )?;

    let mut unsorted_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &unsorted_queue_from_passthrough,
        &unsorted_queue_from_fsm,
    )?;

    if let Some(wit) = initial_queue_witness {
        unsorted_queue.witness = wit;
    }

    let intermediate_sorted_queue_from_passthrough = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .head_state,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .tail_state,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .num_items,
    )?;

    // it must be trivial
    intermediate_sorted_queue_from_passthrough
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let intermediate_sorted_queue_from_fsm = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .intermediate_sorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .intermediate_sorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .intermediate_sorted_queue_state
            .num_items,
    )?;

    let mut intermediate_sorted_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &intermediate_sorted_queue_from_passthrough,
        &intermediate_sorted_queue_from_fsm,
    )?;

    if let Some(wit) = intermediate_sorted_queue_witness {
        intermediate_sorted_queue.witness = wit;
    }

    let final_sorted_queue_from_fsm = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .final_result_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .final_result_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .final_result_queue_state
            .num_items,
    )?;

    let mut final_sorted_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &StorageLogQueue::empty(),
        &final_sorted_queue_from_fsm,
    )?;

    // get challenges for permutation argument

    let mut fs_input = vec![];
    fs_input.push(unsorted_queue_from_passthrough.get_tail_state());
    fs_input.push(unsorted_queue_from_passthrough.len().inner);
    fs_input.push(intermediate_sorted_queue_from_passthrough.get_tail_state());
    fs_input.push(intermediate_sorted_queue_from_passthrough.len().inner);

    // this is a permutation proof through the grand product
    use crate::glue::optimizable_queue::variable_length_absorb_into_empty_state;
    let mut sponge_state = variable_length_absorb_into_empty_state(cs, &fs_input, round_function)?;

    let mut taken = 0; // up to absorbtion length
    let mut fs_challenges = vec![];
    for _ in 0..NUM_PERMUTATION_ARG_CHALLENGES {
        if taken == 2 {
            // run round
            sponge_state = round_function.round_function(cs, sponge_state)?;
            taken = 0;
        }

        let challenge = sponge_state[taken];
        fs_challenges.push(challenge);

        taken += 1;
    }

    let fs_challenges: [Num<E>; NUM_PERMUTATION_ARG_CHALLENGES] = fs_challenges.try_into().unwrap();

    let initial_lhs = Num::conditionally_select(
        cs,
        &structured_input.start_flag,
        &Num::Constant(E::Fr::one()),
        &structured_input.hidden_fsm_input.lhs_accumulator,
    )?;

    let initial_rhs = Num::conditionally_select(
        cs,
        &structured_input.start_flag,
        &Num::Constant(E::Fr::one()),
        &structured_input.hidden_fsm_input.rhs_accumulator,
    )?;

    // there is no code at address 0 in our case, so we can formally use it for all the purposes
    let previous_packed_key = Num::conditionally_select(
        cs,
        &structured_input.start_flag,
        &Num::zero(),
        &structured_input.hidden_fsm_input.previous_packed_key,
    )?;

    // there is no code at address 0 in our case, so we can formally use it for all the purposes
    let previous_item = StorageLogRecord::conditionally_select(
        cs,
        &structured_input.start_flag,
        &StorageLogRecord::empty(),
        &structured_input.hidden_fsm_input.previous_item,
    )?;

    let (new_lhs, new_rhs, previous_packed_key, previous_item) =
        repack_and_prove_events_rollbacks_inner(
            cs,
            initial_lhs,
            initial_rhs,
            &mut unsorted_queue,
            &mut intermediate_sorted_queue,
            &mut final_sorted_queue,
            structured_input.start_flag,
            fs_challenges,
            previous_packed_key,
            previous_item,
            round_function,
            limit,
        )?;

    let unsorted_is_empty = unsorted_queue.is_empty(cs)?;
    let sorted_is_empty = intermediate_sorted_queue.is_empty(cs)?;

    Boolean::enforce_equal(cs, &unsorted_is_empty, &sorted_is_empty)?;

    let completed = smart_and(cs, &[unsorted_is_empty, sorted_is_empty])?;
    Num::conditionally_enforce_equal(cs, &completed, &new_lhs, &new_rhs)?;

    // form the final state
    structured_input.hidden_fsm_output.previous_packed_key = previous_packed_key;
    structured_input.hidden_fsm_output.previous_item = previous_item;
    structured_input.hidden_fsm_output.lhs_accumulator = new_lhs;
    structured_input.hidden_fsm_output.rhs_accumulator = new_rhs;

    structured_input
        .hidden_fsm_output
        .initial_unsorted_queue_state = unsorted_queue.into_state();
    structured_input
        .hidden_fsm_output
        .intermediate_sorted_queue_state = intermediate_sorted_queue.into_state();

    use crate::glue::optimizable_queue::FixedWidthEncodingGenericQueue;

    structured_input.completion_flag = completed;

    let final_queue_for_observable_output = FixedWidthEncodingGenericQueue::conditionally_select(
        cs,
        &completed,
        &final_sorted_queue,
        &FixedWidthEncodingGenericQueue::empty(),
    )?;

    structured_input.observable_output.final_queue_state =
        final_queue_for_observable_output.into_state();

    structured_input.hidden_fsm_output.final_result_queue_state = final_sorted_queue.into_state();

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

pub fn repack_and_prove_events_rollbacks_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    mut lhs: Num<E>,
    mut rhs: Num<E>,
    unsorted_queue: &mut StorageLogQueue<E>,
    intermediate_sorted_queue: &mut StorageLogQueue<E>,
    result_queue: &mut StorageLogQueue<E>,
    is_start: Boolean,
    fs_challenges: [Num<E>; NUM_PERMUTATION_ARG_CHALLENGES],
    mut previous_packed_key: Num<E>,
    mut previous_item: StorageLogRecord<E>,
    round_function: &R,
    limit: usize,
) -> Result<(Num<E>, Num<E>, Num<E>, StorageLogRecord<E>), SynthesisError> {
    assert!(limit <= u32::MAX as usize);

    // we can recreate it here, there are two cases:
    // - we are 100% empty, but it's the only circuit in this case
    // - otherwise we continue, and then it's not trivial
    let no_work = unsorted_queue.is_empty(cs)?;
    let mut previous_is_trivial = smart_or(cs, &[no_work, is_start])?;

    unsorted_queue
        .len()
        .inner
        .enforce_equal(cs, &intermediate_sorted_queue.len().inner)?;

    let additive_part = fs_challenges[NUM_PERMUTATION_ARG_CHALLENGES - 1];

    // reallocate and simultaneously collapse rollbacks

    const PACKED_WIDTHS: [usize; 1] = [33];

    for _cycle in 0..limit {
        let original_is_empty = unsorted_queue.is_empty(cs)?;
        let sorted_is_empty = intermediate_sorted_queue.is_empty(cs)?;
        Boolean::enforce_equal(cs, &original_is_empty, &sorted_is_empty)?;

        let should_pop = original_is_empty.not();
        let is_trivial = should_pop.not();

        let original_encoding = unsorted_queue.pop_first_encoding_only::<_, _, 2, 3>(
            cs,
            &should_pop,
            round_function,
        )?;
        let (sorted_item, sorted_encoding) = intermediate_sorted_queue
            .pop_first_and_return_encoding(cs, &should_pop, round_function)?;

        // we also ensure that items are "write" unless it's a padding
        can_not_be_false_if_flagged(cs, &sorted_item.r_w_flag, &original_is_empty.not())?;

        assert_eq!(original_encoding.len(), sorted_encoding.len());
        assert_eq!(original_encoding.len(), fs_challenges.len() - 1);
        let mut lhs_lc = LinearCombination::zero();
        let mut rhs_lc = LinearCombination::zero();
        for ((original_el, sorted_el), challenge) in original_encoding
            .into_iter()
            .zip(sorted_encoding.into_iter())
            .zip(fs_challenges.iter())
        {
            let lhs_contribution = original_el.mul(cs, &challenge)?;
            let rhs_contribution = sorted_el.mul(cs, &challenge)?;

            lhs_lc.add_assign_number_with_coeff(&lhs_contribution, E::Fr::one());
            rhs_lc.add_assign_number_with_coeff(&rhs_contribution, E::Fr::one());
        }

        lhs_lc.add_assign_number_with_coeff(&additive_part, E::Fr::one());
        rhs_lc.add_assign_number_with_coeff(&additive_part, E::Fr::one());

        let lhs_contribution = lhs_lc.into_num(cs)?;
        let rhs_contribution = rhs_lc.into_num(cs)?;

        let lhs_candidate = lhs.mul(cs, &lhs_contribution)?;
        let rhs_candidate = rhs.mul(cs, &rhs_contribution)?;

        lhs = Num::conditionally_select(cs, &should_pop, &lhs_candidate, &lhs)?;
        rhs = Num::conditionally_select(cs, &should_pop, &rhs_candidate, &rhs)?;

        // now ensure sorting
        {
            // sanity check - all such logs are "write into the sky"
            can_not_be_false_if_flagged(cs, &sorted_item.r_w_flag, &is_trivial.not())?;

            // check if keys are equal and check a value
            let packed_key = pack_key(cs, (sorted_item.timestamp, sorted_item.rollback))?;

            // ensure sorting for uniqueness timestamp and rollback flag
            // We know that timestamps are unique accross logs, and are also the same between write and rollback
            let (_keys_are_equal, new_key_is_greater) = prepacked_long_comparison(
                cs,
                &[packed_key],
                &[previous_packed_key],
                &PACKED_WIDTHS,
            )?;

            // keys are always ordered no matter what, and are never equal unless it's padding
            can_not_be_false_if_flagged(cs, &new_key_is_greater, &is_trivial.not())?;

            // there are only two cases when keys are equal:
            // - it's a padding element
            // - it's a rollback

            // it's enough to compare timestamps as VM circuit guarantees uniqueness of the if it's not a padding
            let same_log = UInt32::equals(cs, &sorted_item.timestamp, &previous_item.timestamp)?;
            let values_are_equal =
                UInt256::equals(cs, &sorted_item.written_value, &previous_item.written_value)?;
            let should_enforce = smart_and(cs, &[same_log, previous_is_trivial.not()])?;
            can_not_be_false_if_flagged(cs, &values_are_equal, &should_enforce)?;

            let this_item_is_non_trivial_rollback =
                smart_and(cs, &[sorted_item.rollback, is_trivial.not()])?;
            let prevous_item_is_non_trivial_write = smart_and(
                cs,
                &[previous_item.rollback.not(), previous_is_trivial.not()],
            )?;
            let is_sequential_rollback = smart_and(
                cs,
                &[
                    this_item_is_non_trivial_rollback,
                    prevous_item_is_non_trivial_write,
                ],
            )?;
            can_not_be_false_if_flagged(cs, &same_log, &is_sequential_rollback)?;

            // decide if we should add the PREVIOUS into the queue
            // We add only if previous one is not trivial,
            // and it had a different key, and it wasn't rolled back
            let add_to_the_queue = smart_and(
                cs,
                &[
                    previous_is_trivial.not(),
                    same_log.not(),
                    previous_item.rollback.not(),
                ],
            )?;

            // cleanup some fields that are not useful
            let query_to_add = StorageLogRecord {
                address: previous_item.address,
                key: previous_item.key,
                read_value: UInt256::zero(),
                written_value: previous_item.written_value,
                r_w_flag: Boolean::constant(false),
                aux_byte: Byte::zero(),
                rollback: Boolean::constant(false),
                is_service: previous_item.is_service,
                shard_id: previous_item.shard_id,
                tx_number_in_block: previous_item.tx_number_in_block,
                timestamp: UInt32::zero(),
            };

            result_queue.push(cs, &query_to_add, &add_to_the_queue, round_function)?;

            previous_is_trivial = is_trivial;
            previous_item = sorted_item;
            previous_packed_key = packed_key;
        }
    }

    // finalization step - same way, check if last item is not a rollback
    {
        let now_empty = unsorted_queue.is_empty(cs)?;

        let add_to_the_queue = smart_and(
            cs,
            &[
                previous_is_trivial.not(),
                previous_item.rollback.not(),
                now_empty,
            ],
        )?;

        let query_to_add = StorageLogRecord {
            address: previous_item.address,
            key: previous_item.key,
            read_value: UInt256::zero(),
            written_value: previous_item.written_value,
            r_w_flag: Boolean::constant(false),
            aux_byte: Byte::zero(),
            rollback: Boolean::constant(false),
            is_service: previous_item.is_service,
            shard_id: previous_item.shard_id,
            tx_number_in_block: previous_item.tx_number_in_block,
            timestamp: UInt32::zero(),
        };

        result_queue.push(cs, &query_to_add, &add_to_the_queue, round_function)?;
    }

    Ok((lhs, rhs, previous_packed_key, previous_item))
}

pub fn pack_key<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    key_tuple: (UInt32<E>, Boolean),
) -> Result<Num<E>, SynthesisError> {
    let shifts = compute_shifts::<E::Fr>();

    let (timestamp, rollback) = key_tuple;
    let mut lc_0 = LinearCombination::zero();
    lc_0.add_assign_boolean_with_coeff(&rollback, shifts[0]);
    lc_0.add_assign_number_with_coeff(&timestamp.inner, shifts[1]);
    // 32 + 1 = 33 in total
    let value_0 = lc_0.into_num(cs)?;

    Ok(value_0)
}
