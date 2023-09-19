use zkevm_opcode_defs::BOOTLOADER_HEAP_PAGE;

use super::memory_queries_validity::ram_permutation_inout::RamPermutationCycleInputOutput;
use super::*;
use crate::glue::code_unpacker_sha256::memory_query_updated::{MemoryQueriesQueue, RawMemoryQuery};
use crate::glue::memory_queries_validity::ram_permutation_inout::RamPermutationCycleInputOutputWitness;
use crate::glue::sponge_like_optimizable_queue::FixedWidthEncodingSpongeLikeQueueWitness;
use crate::scheduler::queues::FullSpongeLikeQueueState;
use crate::vm::vm_cycle::add_assymmetric_table;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct RamPermutationCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: RamPermutationCycleInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub unsorted_queue_witness:
        FixedWidthEncodingSpongeLikeQueueWitness<E, RawMemoryQuery<E>, 2, 3>,
    #[serde(bound(
        serialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub sorted_queue_witness: FixedWidthEncodingSpongeLikeQueueWitness<E, RawMemoryQuery<E>, 2, 3>,
}

pub fn ram_permutation_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    closed_form_input_witness: Option<RamPermutationCircuitInstanceWitness<E>>,
    round_function: &R,
    limit: usize,
) -> Result<AllocatedNum<E>, SynthesisError> {
    // destructure

    inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    add_assymmetric_table(cs)?;

    let closed_form_input = project_ref!(closed_form_input_witness, closed_form_input).cloned();
    let unsorted_queue_witness =
        project_ref!(closed_form_input_witness, unsorted_queue_witness).cloned();
    let sorted_queue_witness =
        project_ref!(closed_form_input_witness, sorted_queue_witness).cloned();

    // our logic is simple - we either create a queue from "input", or - if it's the first instance of such circuit -
    // from passthrough data

    let mut structured_input =
        RamPermutationCycleInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone())?;

    // dbg!(&structured_input.hidden_fsm_input.num_nondeterministic_writes);
    // dbg!(structured_input.fsm_input.current_unsorted_queue_state.clone().create_witness());

    let unsorted_queue_from_fsm_input = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .tail,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .length,
    )?;

    let unsorted_queue_from_passthrough = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .unsorted_queue_initial_state
            .head,
        structured_input
            .observable_input
            .unsorted_queue_initial_state
            .tail,
        structured_input
            .observable_input
            .unsorted_queue_initial_state
            .length,
    )?;
    // it must be trivial
    for el in unsorted_queue_from_passthrough.head_state.iter() {
        el.enforce_equal(cs, &Num::zero())?;
    }

    let mut unsorted_queue = MemoryQueriesQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &unsorted_queue_from_passthrough,
        &unsorted_queue_from_fsm_input,
    )?;

    // dbg!(unsorted_queue.clone().into_state().create_witness());

    if let Some(wit) = unsorted_queue_witness {
        unsorted_queue.witness = wit;
    }

    // same logic for sorted one

    let sorted_queue_from_fsm_input = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_sorted_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .current_sorted_queue_state
            .tail,
        structured_input
            .hidden_fsm_input
            .current_sorted_queue_state
            .length,
    )?;

    let sorted_queue_from_passthrough = MemoryQueriesQueue::from_raw_parts(
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
    for el in sorted_queue_from_passthrough.head_state.iter() {
        el.enforce_equal(cs, &Num::zero())?;
    }

    let mut sorted_queue = MemoryQueriesQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &sorted_queue_from_passthrough,
        &sorted_queue_from_fsm_input,
    )?;

    // dbg!(sorted_queue.clone().into_state().create_witness());

    if let Some(wit) = sorted_queue_witness {
        sorted_queue.witness = wit;
    }

    // redraw the challenges. We would pay for it anyway

    let mut fs_input = vec![];
    fs_input.extend_from_slice(&unsorted_queue.tail_state);
    // length must be original of the full queue
    fs_input.push(
        structured_input
            .observable_input
            .unsorted_queue_initial_state
            .length
            .inner,
    );
    fs_input.extend_from_slice(&sorted_queue.tail_state);
    fs_input.push(
        structured_input
            .observable_input
            .sorted_queue_initial_state
            .length
            .inner,
    );

    const NUM_PERMUTATION_ARG_CHALLENGES: usize = 3;

    // this is a permutation proof through the grand product
    // we need to make irreducible polynomials over every challenge, so we elaborate a little here
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

    let fs_challenges: [Num<E>; 3] = fs_challenges.try_into().unwrap();

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

    let num_nondeterministic_writes = UInt32::conditionally_select(
        cs,
        &structured_input.start_flag,
        &UInt32::zero(),
        &structured_input
            .hidden_fsm_input
            .num_nondeterministic_writes,
    )?;

    // walk over queues, accumulate grand products, and ensure sorting

    let (
        (new_lhs, new_rhs),
        (last_element_sorting_key, last_element_comparison_key, last_element_values, last_is_ptr),
        num_nondeterministic_writes,
    ) = partial_accumulate_inner(
        cs,
        &mut unsorted_queue,
        &mut sorted_queue,
        &fs_challenges,
        structured_input.start_flag,
        initial_lhs,
        initial_rhs,
        structured_input.hidden_fsm_input.previous_sorting_key,
        structured_input.hidden_fsm_input.previous_full_key,
        structured_input.hidden_fsm_input.previous_values_pair,
        structured_input.hidden_fsm_input.previous_is_ptr,
        num_nondeterministic_writes,
        // structured_input.observable_input.unsorted_queue_initial_state.length,
        round_function,
        limit,
    )?;

    let unsorted_is_empty = unsorted_queue.is_empty(cs)?;
    let sorted_is_empty = sorted_queue.is_empty(cs)?;

    Boolean::enforce_equal(cs, &unsorted_is_empty, &sorted_is_empty)?;

    let completed = smart_and(cs, &[unsorted_is_empty, sorted_is_empty])?;
    Num::conditionally_enforce_equal(cs, &completed, &new_lhs, &new_rhs)?;
    Num::conditionally_enforce_equal(
        cs,
        &completed,
        &num_nondeterministic_writes.inner,
        &structured_input
            .observable_input
            .non_deterministic_bootloader_memory_snapshot_length
            .inner,
    )?;

    structured_input.hidden_fsm_output.previous_sorting_key = last_element_sorting_key;
    structured_input.hidden_fsm_output.previous_full_key = last_element_comparison_key;
    structured_input.hidden_fsm_output.previous_values_pair = last_element_values;
    structured_input.hidden_fsm_output.previous_is_ptr = last_is_ptr;

    structured_input.hidden_fsm_output.lhs_accumulator = new_lhs;
    structured_input.hidden_fsm_output.rhs_accumulator = new_rhs;

    structured_input
        .hidden_fsm_output
        .num_nondeterministic_writes = num_nondeterministic_writes;

    structured_input
        .hidden_fsm_output
        .current_unsorted_queue_state = unsorted_queue.into_state();
    structured_input
        .hidden_fsm_output
        .current_sorted_queue_state = sorted_queue.into_state();

    structured_input.completion_flag = completed;

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = closed_form_input {
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

const SORTING_KEY_ENCODING_LENGTHS: [usize; 1] = [32 + 32 + 32];

fn sorting_key_comparison_key_value_and_rw_ptr_flags<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    query: &RawMemoryQuery<E>,
) -> Result<(Num<E>, Num<E>, [Num<E>; 2], Boolean, Boolean), SynthesisError> {
    // key is memory_page | index | ts_marker | ts
    let RawMemoryQuery {
        timestamp,
        memory_index,
        memory_page,
        rw_flag,
        value_residual,
        value,
        value_is_ptr,
        ..
    } = query;

    let shifts = compute_shifts::<E::Fr>();
    let mut lc = LinearCombination::zero();
    let mut shift = 0;
    lc.add_assign_number_with_coeff(&memory_index.inner, shifts[shift]);
    shift += 32;
    lc.add_assign_number_with_coeff(&memory_page.inner, shifts[shift]);
    shift += 32;
    assert!(shift <= E::Fr::CAPACITY as usize);
    let comparison_key = lc.into_num(cs)?;
    let k_width = shift;

    let mut lc = LinearCombination::zero();
    let mut shift = 0;
    lc.add_assign_number_with_coeff(&timestamp.inner, shifts[shift]);
    shift += 32;
    lc.add_assign_number_with_coeff(&comparison_key, shifts[shift]);
    shift += k_width;
    assert!(shift <= E::Fr::CAPACITY as usize);
    assert_eq!(shift, SORTING_KEY_ENCODING_LENGTHS[0]);
    let sorting_key = lc.into_num(cs)?;

    let v0 = *value;
    let v1 = value_residual.inner;

    let t = (
        sorting_key,
        comparison_key,
        [v0, v1],
        *rw_flag,
        *value_is_ptr,
    );

    Ok(t)
}

pub fn partial_accumulate_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    unsorted_queue: &mut MemoryQueriesQueue<E, 2, 3>,
    sorted_queue: &mut MemoryQueriesQueue<E, 2, 3>,
    fs_challenges: &[Num<E>; 3],
    is_start: Boolean,
    initial_lhs: Num<E>,
    initial_rhs: Num<E>,
    previous_sorting_key: Num<E>,
    previous_comparison_key: Num<E>,
    previous_element_values: [Num<E>; 2],
    previous_is_ptr: Boolean,
    mut num_nondeterministic_writes: UInt32<E>,
    // full_unsorted_queue_length: UInt32<E>,
    round_function: &R,
    limit: usize,
) -> Result<
    (
        (Num<E>, Num<E>),
        (Num<E>, Num<E>, [Num<E>; 2], Boolean),
        UInt32<E>,
    ),
    SynthesisError,
> {
    assert!(limit <= u32::MAX as usize);
    let mut lhs = initial_lhs;
    let mut rhs = initial_rhs;

    let [challenge_0, challenge_1, additive_part] = *fs_challenges;

    let [v0, v1] = previous_element_values;
    let mut previous_key_value = (
        previous_sorting_key,
        previous_comparison_key,
        (v0, v1),
        previous_is_ptr,
    );

    for _cycle in 0..limit {
        let can_pop_from_unsorted_queue = unsorted_queue.is_empty(cs)?.not();
        let can_pop_from_sorted_queue = sorted_queue.is_empty(cs)?.not();
        Boolean::enforce_equal(cs, &can_pop_from_unsorted_queue, &can_pop_from_sorted_queue)?;
        let can_pop = can_pop_from_unsorted_queue;
        // we do not need any information about unsorted element other than it's encoding
        let unsorted_item_encoding =
            unsorted_queue.pop_first_encoding_only(cs, &can_pop, round_function)?;
        // let unsorted_item_encoding = unsorted_queue.pop_first_encoding_only(cs, &can_pop, round_function)?;
        let (sorted_item, sorted_item_encoding) =
            sorted_queue.pop_first_and_return_encoding(cs, &can_pop, round_function)?;

        // We use an optimization that we fill the bootloader HEAP (and only it!) non-deterministically by claiming that some
        // queue state (sponge) encodes a queue with N elements, where elements are:
        // - only writes
        // - at timestamp 0
        // - into bootloader heap page

        // During permutation argument those elements are no longer adjusted after sorting, but we still
        // count them, and if at the end of the argument number of such encountered arguments matches the initially declared
        // one then all those non-deterministic writes have indeed the properties described above, because:
        // - VM, code unpacks and  precompiles can not add any writes at timestamp 0, or in general before TS 1024 (start of VM)
        // - total length of sorted and unsorted queues match
        // - set of elements in both queues is the same
        // so number of non-deterministic writes will match if and only if all of those pass the check below: write, ts == 0, into heap page
        {
            let ts_is_zero = sorted_item.timestamp.is_zero(cs)?;
            let page_is_bootloader_heap = Num::equals(
                cs,
                &sorted_item.memory_page.inner,
                &UInt32::from_uint(BOOTLOADER_HEAP_PAGE).inner,
            )?;
            let is_write = sorted_item.rw_flag;
            let is_ptr = sorted_item.value_is_ptr;
            let is_nondeterministic_write = smart_and(
                cs,
                &[
                    can_pop,
                    ts_is_zero,
                    page_is_bootloader_heap,
                    is_write,
                    is_ptr.not(),
                ],
            )?;
            num_nondeterministic_writes = num_nondeterministic_writes
                .conditionally_increment_unchecked(cs, &is_nondeterministic_write)?;
        }
        {
            // either continue the argument or do nothin
            let (previous_sk, previous_ck, (previous_v0, previous_v1), previous_is_ptr) =
                previous_key_value;
            let (sk, ck, [v0, v1], rw_flag, is_ptr) =
                sorting_key_comparison_key_value_and_rw_ptr_flags(cs, &sorted_item)?;

            // ensure sorting
            let (keys_are_equal, previous_key_is_greater) = prepacked_long_comparison(
                cs,
                &[previous_sk],
                &[sk],
                &SORTING_KEY_ENCODING_LENGTHS,
            )?;
            let keys_are_in_ascending_order =
                smart_and(cs, &[previous_key_is_greater.not(), keys_are_equal.not()])?;
            if _cycle != 0 {
                can_not_be_false_if_flagged(cs, &keys_are_in_ascending_order, &can_pop)?;
            } else {
                let should_enforce = smart_and(cs, &[can_pop, is_start.not()])?;
                can_not_be_false_if_flagged(cs, &keys_are_in_ascending_order, &should_enforce)?;
            }

            let same_memory_cell = Num::equals(cs, &previous_ck, &ck)?;

            let v0_equal = Num::equals(cs, &previous_v0, &v0)?;
            let v1_equal = Num::equals(cs, &previous_v1, &v1)?;

            // check uninit read
            let t0 = v0.is_zero(cs)?;
            let t1 = v1.is_zero(cs)?;
            let is_zero = smart_and(cs, &[t0, t1, is_ptr.not()])?;
            let ptr_equality = Boolean::xor(cs, &previous_is_ptr, &is_ptr)?.not();

            // we only have a difference in these flags at the first step
            if _cycle != 0 {
                let read_uninitialized = smart_and(cs, &[same_memory_cell.not(), rw_flag.not()])?;
                can_not_be_false_if_flagged(cs, &is_zero, &read_uninitialized)?;

                // check standard RW validity
                let value_equal = smart_and(cs, &[v0_equal, v1_equal, ptr_equality])?;
                let check_equality = smart_and(cs, &[same_memory_cell, rw_flag.not()])?;
                can_not_be_false_if_flagged(cs, &value_equal, &check_equality)?;
            } else {
                // see if we continue the argument then all our checks should be valid,
                // otherwise only read uninit should be enforced

                // if we start a fresh argument then our comparison
                let read_uninitialized_if_continue =
                    smart_and(cs, &[is_start.not(), same_memory_cell.not(), rw_flag.not()])?;
                let read_uninit_if_at_the_start = smart_and(cs, &[is_start, rw_flag.not()])?;
                let should_enforce = smart_or(
                    cs,
                    &[read_uninitialized_if_continue, read_uninit_if_at_the_start],
                )?;
                can_not_be_false_if_flagged(cs, &is_zero, &should_enforce)?;

                // check standard RW validity, but it can break if we are at the very start
                let value_equal = smart_and(cs, &[v0_equal, v1_equal, ptr_equality])?;
                let check_equality =
                    smart_and(cs, &[same_memory_cell, rw_flag.not(), is_start.not()])?;
                can_not_be_false_if_flagged(cs, &value_equal, &check_equality)?;
            }

            previous_key_value = (sk, ck, (v0, v1), is_ptr);
        }

        // if we did pop then accumulate
        let mut lhs_contribution = LinearCombination::zero();
        lhs_contribution.add_assign_number_with_coeff(&additive_part, E::Fr::one());
        let mut rhs_contribution = LinearCombination::zero();
        rhs_contribution.add_assign_number_with_coeff(&additive_part, E::Fr::one());

        assert_eq!(unsorted_item_encoding.len(), 2);
        assert_eq!(sorted_item_encoding.len(), 2);

        for ((unsorted_contribution, sorted_contribution), challenge) in unsorted_item_encoding
            .iter()
            .zip(sorted_item_encoding.iter())
            .zip([challenge_0, challenge_1].iter())
        {
            let l = unsorted_contribution.mul(cs, challenge)?;
            lhs_contribution.add_assign_number_with_coeff(&l, E::Fr::one());
            let r = sorted_contribution.mul(cs, challenge)?;
            rhs_contribution.add_assign_number_with_coeff(&r, E::Fr::one());
        }

        let lhs_contribution = lhs_contribution.into_num(cs)?;
        let rhs_contribution = rhs_contribution.into_num(cs)?;
        let new_lhs = lhs.mul(cs, &lhs_contribution)?;
        let new_rhs = rhs.mul(cs, &rhs_contribution)?;

        lhs = Num::conditionally_select(cs, &can_pop, &new_lhs, &lhs)?;
        rhs = Num::conditionally_select(cs, &can_pop, &new_rhs, &rhs)?;
    }

    let (last_sk, last_k, (last_v0, last_v1), last_is_ptr) = previous_key_value;

    Ok((
        (lhs, rhs),
        (last_sk, last_k, [last_v0, last_v1], last_is_ptr),
        num_nondeterministic_writes,
    ))
}
