use crate::glue::sponge_like_optimizable_queue::FixedWidthEncodingSpongeLikeQueueWitness;
use crate::scheduler::queues::FullSpongeLikeQueueState;

use super::*;
use super::input::*;
use super::grand_product::*;

pub fn memory_validity_entry_point<
    E: Engine, 
    CS: ConstraintSystem<E>, 
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>
>(
    cs: &mut CS,
    input_witness: Option<MemoryArgumentStructuredInputWitness<E>>,
    unsorted_queue_witness: Option<FixedWidthEncodingSpongeLikeQueueWitness<E, RawMemoryQuery<E>, 2, 3>>,
    sorted_queue_witness: Option<FixedWidthEncodingSpongeLikeQueueWitness<E, RawMemoryQuery<E>, 2, 3>>,
    round_function: &R,
    limit: usize,
    reporting_function: Option<Box<dyn FnOnce(((E::Fr, E::Fr), (E::Fr, E::Fr, [E::Fr; 2]))) -> ()>>, // (lhs, rhs, last elements)
) -> Result<(), SynthesisError> {
    let mut input = MemoryArgumentStructuredInput::alloc_from_witness(cs, input_witness)?;

    let mut unsorted_queue = MemoryAccessQueue::from_raw_parts(
        cs,
        input.original_queue_initial_state.head,
        input.original_queue_initial_state.tail,
        input.original_queue_initial_state.length
    )?;
    if let Some(wit) = unsorted_queue_witness {
        unsorted_queue.witness = wit;
    }

    let mut sorted_queue = MemoryAccessQueue::from_raw_parts(
        cs,
        input.sorted_queue_initial_state.head,
        input.sorted_queue_initial_state.tail,
        input.sorted_queue_initial_state.length
    )?;
    if let Some(wit) = sorted_queue_witness {
        sorted_queue.witness = wit;
    }

    let ((new_lhs, new_rhs), (last_element_sorting_key, last_element_full_key, last_element_values)) = partial_accumulate_inner(
        cs,
        &mut unsorted_queue,
        &mut sorted_queue,
        &input.fs_challenges,
        input.lhs_accumulator,
        input.rhs_accumulator,
        input.continue_argument,
        input.last_element_sorting_key,
        input.last_element_full_key,
        input.last_element_values,
        round_function,
        limit
    )?;

    // we expect that someone has already split the queue into chunks
    // of a proper size, so this chunk must be empty now
    unsorted_queue.enforce_to_be_empty(cs)?;
    sorted_queue.enforce_to_be_empty(cs)?;

    input.result_lhs_accumulator = new_lhs;
    input.result_rhs_accumulator = new_rhs;
    input.result_last_element_sorting_key = last_element_sorting_key;
    input.result_last_element_full_key = last_element_full_key;
    input.result_last_element_values = last_element_values;

    let input_commitment = commit_encodable_item(cs, &input, round_function)?;
    let input_commitment_witness = input_commitment.get_value();
    let public_input = AllocatedNum::alloc_input(
        cs,
        || input_commitment_witness.grab()
    )?;
    public_input.enforce_equal(cs, &input_commitment.get_variable())?;

    // report
    if let Some(wit) = input.create_witness() {
        if let Some(reporting_function) = reporting_function {
            let MemoryArgumentStructuredInputWitness { 
                result_lhs_accumulator, 
                result_rhs_accumulator,
                result_last_element_sorting_key,
                result_last_element_full_key,
                result_last_element_values,
                .. 
            } = wit;

            reporting_function(
                (
                    (result_lhs_accumulator, result_rhs_accumulator),
                    (result_last_element_sorting_key, result_last_element_full_key, result_last_element_values)
                )
            );
        }
    }

    Ok(())
}