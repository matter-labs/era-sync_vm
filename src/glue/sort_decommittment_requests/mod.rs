use super::*;
use crate::glue::traits::*;
use crate::scheduler::queues::*;
use crate::vm::vm_cycle::add_assymmetric_table;

pub mod input;

// This is a sorter of logs that are kind-of "pure", e.g. event emission or L2 -> L1 messages.
// Those logs do not affect a global state and may either be rolled back in full or not.
// We identify equality of logs using "timestamp" field that is a monotonic unique counter
// across the block

use self::input::*;

pub fn sort_and_deduplicate_code_decommittments_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<CodeDecommittmentsDeduplicatorInstanceWitness<E>>,
    round_function: &R,
    limit: usize,
) -> Result<AllocatedNum<E>, SynthesisError> {
    // as usual we assume that a caller of this fuunction has already split input queue,
    // so it can be comsumed in full

    inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    add_assymmetric_table(cs)?;

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let initial_queue_witness = project_ref!(witness, initial_queue_witness).cloned();
    let sorted_queue_witness = project_ref!(witness, sorted_queue_witness).cloned();
    let previous_record_witness = project_ref!(witness, previous_record_witness).cloned();

    let mut structured_input = CodeDecommittmentsDeduplicatorInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    )?;

    let queue_states_from_fsm = [
        &structured_input.hidden_fsm_input.initial_log_queue_state,
        &structured_input.hidden_fsm_input.sorted_queue_state,
        &structured_input.hidden_fsm_input.final_queue_state,
    ];

    let [initial_log_queue_state_from_fsm, sorted_queue_state_from_fsm, final_queue_state_from_fsm] =
        queue_states_from_fsm
            .map(|el| DecommitQueue::from_raw_parts(cs, el.head, el.tail, el.length));

    let initial_queue_from_passthrough = DecommitQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .initial_log_queue_state
            .head,
        structured_input
            .observable_input
            .initial_log_queue_state
            .tail,
        structured_input
            .observable_input
            .initial_log_queue_state
            .length,
    )?;

    let mut initial_queue = DecommitQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &initial_queue_from_passthrough,
        &initial_log_queue_state_from_fsm?,
    )?;

    // passthrough must be trivial
    for el in initial_queue_from_passthrough.head_state.iter() {
        el.enforce_equal(cs, &Num::zero())?;
    }

    if let Some(wit) = initial_queue_witness {
        initial_queue.witness = wit;
    }

    let intermediate_sorted_queue_from_passthrough = DecommitQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .sorted_queue_initial_state
            .head,
        structured_input
            .observable_input
            .sorted_queue_initial_state
            .tail,
        structured_input
            .observable_input
            .sorted_queue_initial_state
            .length,
    )?;

    // it must be trivial
    for el in intermediate_sorted_queue_from_passthrough.head_state.iter() {
        el.enforce_equal(cs, &Num::zero())?;
    }

    let mut intermediate_sorted_queue = DecommitQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &intermediate_sorted_queue_from_passthrough,
        &sorted_queue_state_from_fsm?,
    )?;

    if let Some(wit) = sorted_queue_witness {
        intermediate_sorted_queue.witness = wit;
    }

    let final_sorted_queue_empty = DecommitQueue::<E, 2, 3>::empty();

    let mut final_sorted_queue = DecommitQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &final_sorted_queue_empty,
        &final_queue_state_from_fsm?,
    )?;

    let mut fs_input = vec![];
    fs_input.extend_from_slice(&initial_queue_from_passthrough.get_tail_state());
    fs_input.push(initial_queue_from_passthrough.len().inner);
    fs_input.extend_from_slice(&intermediate_sorted_queue_from_passthrough.get_tail_state());
    fs_input.push(intermediate_sorted_queue_from_passthrough.len().inner);

    // form challenges for permutation proof through the grand product
    use crate::glue::optimizable_queue::variable_length_absorb_into_empty_state;
    let mut sponge_state = variable_length_absorb_into_empty_state(cs, &fs_input, round_function)?;

    let mut taken = 0; // up to absorbtion length
    let mut fs_challenges = vec![];
    for _ in 0..(DecommitHash::<E>::CIRCUIT_ENCODING_LEN + 1) {
        if taken == 2 {
            // run round
            sponge_state = round_function.round_function(cs, sponge_state)?;
            taken = 0;
        }

        let challenge = sponge_state[taken];
        fs_challenges.push(challenge);

        taken += 1;
    }
    assert_eq!(
        fs_challenges.len(),
        DecommitHash::<E>::CIRCUIT_ENCODING_LEN + 1
    );

    let additive_part = fs_challenges.pop().unwrap();

    let mut grand_products = <[Num<E>; 2]>::conditionally_select(
        cs,
        &structured_input.start_flag,
        &[Num::one(); 2],
        &structured_input.hidden_fsm_input.grand_products,
    )?;

    let mut previous_packed_key = structured_input.hidden_fsm_input.previous_packed_key;
    let mut previous_item_is_trivial = structured_input.hidden_fsm_input.previous_item_is_trivial;
    let mut first_encountered_timestamp = structured_input
        .hidden_fsm_input
        .first_encountered_timestamp;
    let previous_record_encoding = structured_input.hidden_fsm_input.previous_record_encoding;
    let mut previous_record = DecommitQuery::allocate_and_prove_encoding(
        cs,
        &previous_record_encoding,
        previous_record_witness,
    )?;

    let completed = sort_and_deduplicate_code_decommittments_inner(
        cs,
        &mut initial_queue,
        &mut intermediate_sorted_queue,
        &mut final_sorted_queue,
        &mut grand_products,
        fs_challenges.clone().try_into().unwrap(),
        additive_part,
        &mut previous_packed_key,
        &mut previous_item_is_trivial,
        &mut first_encountered_timestamp,
        &mut previous_record,
        &structured_input.start_flag,
        round_function,
        limit,
    )?;

    // form the final state
    structured_input.observable_output = CodeDecommittmentsDeduplicatorOutputData::empty();

    structured_input.hidden_fsm_output = CodeDecommittmentsDeduplicatorFSMInputOutput::empty();
    structured_input.hidden_fsm_output.initial_log_queue_state = initial_queue.into_state();
    structured_input.hidden_fsm_output.sorted_queue_state = intermediate_sorted_queue.into_state();
    structured_input.hidden_fsm_output.final_queue_state = final_sorted_queue.into_state();
    structured_input.hidden_fsm_output.grand_products = grand_products;
    structured_input.hidden_fsm_output.previous_packed_key = previous_packed_key;
    structured_input.hidden_fsm_output.previous_item_is_trivial = previous_item_is_trivial;
    structured_input
        .hidden_fsm_output
        .first_encountered_timestamp = first_encountered_timestamp;
    structured_input.hidden_fsm_output.previous_record_encoding = previous_record.encode(cs)?;

    structured_input.observable_output.final_queue_state =
        FullSpongeLikeQueueState::conditionally_select(
            cs,
            &completed,
            &structured_input.hidden_fsm_output.final_queue_state,
            &structured_input.observable_output.final_queue_state,
        )?;

    structured_input.completion_flag = completed;

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = structured_input_witness {
            assert_eq!(circuit_result, passed_input);
        }
    }

    use crate::inputs::ClosedFormInputCompactForm;
    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    use crate::glue::optimizable_queue::commit_encodable_item;
    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();
    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;

    Ok(public_input)
}

pub fn sort_and_deduplicate_code_decommittments_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    original_queue: &mut DecommitQueue<E, 2, 3>,
    sorted_queue: &mut DecommitQueue<E, 2, 3>,
    result_queue: &mut DecommitQueue<E, 2, 3>,
    grand_products: &mut [Num<E>; 2],
    fs_challenges: [Num<E>; 2],
    additive_part: Num<E>,
    previous_packed_key: &mut [Num<E>; 2],
    previous_item_is_trivial: &mut Boolean,
    first_encountered_timestamp: &mut UInt32<E>,
    previous_record: &mut DecommitQuery<E>,
    start_flag: &Boolean,
    round_function: &R,
    limit: usize,
) -> Result<Boolean, SynthesisError> {
    assert!(limit <= u32::MAX as usize);
    original_queue
        .len()
        .inner
        .enforce_equal(cs, &sorted_queue.len().inner)?;

    // reallocate in a proper order
    let mut sorted_items = vec![];
    let mut triviality_flags = vec![];

    for _cycle in 0..limit {
        let original_is_empty = original_queue.is_empty(cs)?;
        let sorted_is_empty = sorted_queue.is_empty(cs)?;
        Boolean::enforce_equal(cs, &original_is_empty, &sorted_is_empty)?;

        let should_pop = original_is_empty.not();

        let original_encoding =
            original_queue.pop_first_encoding_only::<_, _>(cs, &should_pop, round_function)?;
        let (sorted_item, sorted_encoding) =
            sorted_queue.pop_first_and_return_encoding(cs, &should_pop, round_function)?;

        // we make encoding that is the same as defined for timestamped item
        triviality_flags.push(sorted_is_empty);
        sorted_items.push(sorted_item);

        assert_eq!(original_encoding.len(), sorted_encoding.len());
        assert_eq!(original_encoding.len(), fs_challenges.len());
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

        let lhs_candidate = grand_products[0].mul(cs, &lhs_contribution)?;
        let rhs_candidate = grand_products[1].mul(cs, &rhs_contribution)?;

        grand_products[0] =
            Num::conditionally_select(cs, &should_pop, &lhs_candidate, &grand_products[0])?;
        grand_products[1] =
            Num::conditionally_select(cs, &should_pop, &rhs_candidate, &grand_products[1])?;
    }

    // if this circuit is the last one the queues must be empty and grand products must be equal
    let completed = original_queue.is_empty(cs)?;
    let sorted_queue_is_empty = sorted_queue.is_empty(cs)?;
    Boolean::enforce_equal(cs, &completed, &sorted_queue_is_empty)?;

    Num::conditionally_enforce_equal(cs, &completed, &grand_products[0], &grand_products[1])?;

    let it = sorted_items.into_iter().zip(triviality_flags.into_iter());

    // we uniquely identify by the timestamp value, and sort such that if there
    // exists a log with the same timestamp and with a rollback flag
    // then it immediately follows

    // now resolve a logic
    let mut first_iter = true;
    for (record, is_trivial) in it {
        if first_iter {
            // first one must always be unique
            can_not_be_false_if_flagged(cs, &is_trivial.not(), &Boolean::Constant(true))?;
            can_not_be_false_if_flagged(cs, &record.is_first, &start_flag)?;
        }

        // check if keys are equal and check a value
        let packed_key = pack_key(cs, (record.clone().root_hash.as_u256(), record.timestamp))?;

        // ensure sorting for uniqueness timestamp and rollback flag
        // We know that timestamps are unique accross logs, and are also the same between write and rollback
        let (_keys_are_equal, new_key_is_greater) =
            prepacked_long_comparison(cs, &packed_key, previous_packed_key, &PACKED_WIDTHS)?;

        // keys are always ordered no matter what, and are never equal unless it's padding
        let enforce_must_be_greater = if first_iter {
            Boolean::and(cs, &is_trivial.not(), &start_flag.not())?
        } else {
            is_trivial.not()
        };
        can_not_be_false_if_flagged(cs, &new_key_is_greater, &enforce_must_be_greater)?;

        let same_hash = UInt256::equals(
            cs,
            &previous_record.clone().root_hash.as_u256(),
            &record.clone().root_hash.as_u256(),
        )?;

        // if we get new hash then it my have a "first" marker
        let enforce_must_be_first = if first_iter {
            smart_and(cs, &[same_hash.not(), is_trivial.not(), start_flag.not()])?
        } else {
            smart_and(cs, &[same_hash.not(), is_trivial.not()])?
        };
        can_not_be_false_if_flagged(cs, &record.is_first, &enforce_must_be_first)?;

        // otherwise it should have the same memory page
        let enforce_same_memory_page = if first_iter {
            smart_and(
                cs,
                &[same_hash, previous_item_is_trivial.not(), start_flag.not()],
            )?
        } else {
            smart_and(cs, &[same_hash, previous_item_is_trivial.not()])?
        };
        Num::conditionally_enforce_equal(
            cs,
            &enforce_same_memory_page,
            &record.page.inner,
            &previous_record.page.inner,
        )?;

        // decide if we should add the PREVIOUS into the queue
        let add_to_the_queue = if first_iter {
            smart_and(
                cs,
                &[
                    previous_item_is_trivial.not(),
                    same_hash.not(),
                    start_flag.not(),
                ],
            )?
        } else {
            smart_and(cs, &[previous_item_is_trivial.not(), same_hash.not()])?
        };

        let mut record_to_add = previous_record.clone();
        record_to_add.is_first = Boolean::constant(true); // we use convension to be easier consistent with out of circuit part
        record_to_add.timestamp = *first_encountered_timestamp;
        result_queue.push(cs, &record_to_add, &add_to_the_queue, round_function)?;

        *previous_item_is_trivial = is_trivial;
        // may be update the timestamp
        *first_encountered_timestamp = UInt32::conditionally_select(
            cs,
            &same_hash,
            &first_encountered_timestamp,
            &record.timestamp,
        )?;
        *previous_record = record;
        *previous_packed_key = packed_key;

        first_iter = false;
    }

    // finalization step - push the last one if necessary
    {
        let add_to_the_queue = Boolean::and(cs, &previous_item_is_trivial.not(), &completed)?;

        let mut record_to_add = previous_record.clone();
        record_to_add.is_first = Boolean::constant(true); // we use convension to be easier consistent with out of circuit part
        record_to_add.timestamp = *first_encountered_timestamp;

        result_queue.push(cs, &record_to_add, &add_to_the_queue, round_function)?;
    }

    Ok(completed)
}

const PACKED_WIDTHS: [usize; 2] = [96, 192];

fn pack_key<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    key_tuple: (UInt256<E>, UInt32<E>),
) -> Result<[Num<E>; 2], SynthesisError> {
    let shifts = compute_shifts::<E::Fr>();

    let (hash, timestamp) = key_tuple;

    // LE packing

    let mut shift = 0;
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&timestamp.inner, shifts[shift]);
    shift += 32;
    lc.add_assign_number_with_coeff(&hash.inner[0].inner, shifts[shift]);
    shift += 64;
    assert!(shift <= E::Fr::CAPACITY as usize);
    let value_0 = lc.into_num(cs)?;

    let mut shift = 0;
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&hash.inner[1].inner, shifts[shift]);
    shift += 64;
    lc.add_assign_number_with_coeff(&hash.inner[2].inner, shifts[shift]);
    shift += 64;
    lc.add_assign_number_with_coeff(&hash.inner[3].inner, shifts[shift]);
    shift += 64;
    assert!(shift <= E::Fr::CAPACITY as usize);
    let value_1 = lc.into_num(cs)?;

    Ok([value_0, value_1])
}
