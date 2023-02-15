use super::*;
use cs_derive::*;

use crate::glue::traits::*;
use crate::scheduler::queues::*;
use super::decommit_into_page::*;
use crate::scheduler::queues::FixedWidthEncodingSpongeLikeQueueWitness;

#[derive(Derivative, CSAllocatable, CSWitnessable, CSPackable, CSSelectable, CSEqual, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct DecommitIntoPageStructuredInput<E: Engine> {
    pub memory_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub memory_queue_final_state: FullSpongeLikeQueueState<E>,
    pub decommit_requests_queue_state: FullSpongeLikeQueueState<E>,
    pub initial_ts: UInt32<E>,
    pub final_ts: UInt32<E>,
}

pub fn decommit_into_page_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>
>(
    cs: &mut CS,
    input_witness: Option<DecommitIntoPageStructuredInputWitness<E>>,
    requests_queue_witness: Option<FixedWidthEncodingSpongeLikeQueueWitness<E, DelegatedMemoryWriteRecord<E>, 2, 3>>,
    decommitted_elements_witness: Option<Vec<Vec<BigUint>>>,
    round_function: &R,
    limit: usize,
    reporting_function: Option<Box<dyn FnOnce(FullSpongeLikeQueueStateWitness<E>, u32) -> ()>>, 
) -> Result<(), SynthesisError> {
    // as usual we assume that a caller of this fuunction has already split input queue,
    // so it can be comsumed in full

    let mut input = DecommitIntoPageStructuredInput::alloc_from_witness(cs, input_witness)?;

    let mut requests_queue = DelegatedMemoryWritesQueue::from_raw_parts(
        cs,
        input.decommit_requests_queue_state.head,
        input.decommit_requests_queue_state.tail,
        input.decommit_requests_queue_state.length
    )?;
    if let Some(wit) = requests_queue_witness {
        requests_queue.witness = wit;
    }

    let mut memory_queue = MemoryAccessQueue::from_raw_parts(
        cs,
        input.memory_queue_initial_state.head,
        input.memory_queue_initial_state.tail,
        input.memory_queue_initial_state.length
    )?;

    let initial_ts = input.initial_ts;

    let final_ts = decommit_into_page_inner(
        cs,
        &mut memory_queue,
        requests_queue,
        decommitted_elements_witness,
        round_function,
        initial_ts,
        limit
    )?;

    input.memory_queue_final_state = FullSpongeLikeQueueState {
        length: memory_queue.len(),
        head: memory_queue.get_head_state(),
        tail: memory_queue.get_tail_state()
    };
    input.final_ts = final_ts;

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
            let DecommitIntoPageStructuredInputWitness { 
                final_ts, 
                memory_queue_final_state,
                .. 
            } = wit;

            reporting_function(memory_queue_final_state, final_ts);
        }
    }

    Ok(())
}