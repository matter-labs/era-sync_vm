use super::*;
use crate::precompiles::keccak256::*;
use crate::precompiles::*;
use cs_derive::*;
use zk_evm::precompiles::keccak256::BUFFER_SIZE;

pub mod input;

use self::input::*;

use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;
use crate::scheduler::queues::FullSpongeLikeQueueState;

use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQueriesQueue;
use crate::scheduler::queues::StorageLogQueue;

pub fn keccak256_round_function_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<Keccak256RoundFunctionInstanceWitness<E>>,
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
    let requests_queue_witness = project_ref!(witness, requests_queue_witness).cloned();
    let memory_reads_witness = project_ref!(witness, memory_reads_witness).cloned();

    let mut structured_input = Keccak256RoundFunctionInputOutput::alloc_from_witness(
        cs,
        structured_input_witness.clone(),
    )?;

    let requests_queue_from_fsm_input = StorageLogQueue::from_raw_parts(
        cs,
        structured_input.hidden_fsm_input.log_queue_state.head_state,
        structured_input.hidden_fsm_input.log_queue_state.tail_state,
        structured_input.hidden_fsm_input.log_queue_state.num_items,
    )?;

    let requests_queue_from_passthrough = StorageLogQueue::from_raw_parts(
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

    let mut requests_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &requests_queue_from_passthrough,
        &requests_queue_from_fsm_input,
    )?;

    if let Some(wit) = requests_queue_witness {
        requests_queue.witness = wit;
    }

    let memory_queue_from_fsm_input = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input.hidden_fsm_input.memory_queue_state.head,
        structured_input.hidden_fsm_input.memory_queue_state.tail,
        structured_input.hidden_fsm_input.memory_queue_state.length,
    )?;

    let memory_queue_from_passthrough = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input.observable_input.initial_memory_state.head,
        structured_input.observable_input.initial_memory_state.tail,
        structured_input
            .observable_input
            .initial_memory_state
            .length,
    )?;

    let mut memory_queue = MemoryQueriesQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &memory_queue_from_passthrough,
        &memory_queue_from_fsm_input,
    )?;

    let mut starting_fsm_state = KeccakPrecompileState::empty();
    starting_fsm_state.read_precompile_call = Boolean::constant(true);

    let initial_state = KeccakPrecompileState::conditionally_select(
        cs,
        &structured_input.start_flag,
        &starting_fsm_state,
        &structured_input.hidden_fsm_input.precompile_state,
    )?;

    let final_state = keccak256_precompile_inner(
        cs,
        &mut memory_queue,
        &mut requests_queue,
        memory_reads_witness,
        initial_state,
        round_function,
        limit,
    )?;

    let final_memory_state = memory_queue.into_state();
    let final_requets_state = requests_queue.into_state();

    // form the final state
    let done = final_state.completed;
    structured_input.completion_flag = done;
    structured_input.observable_output = PrecompileFunctionOutputData::empty();

    structured_input.observable_output.final_memory_state =
        FullSpongeLikeQueueState::conditionally_select(
            cs,
            &structured_input.completion_flag,
            &final_memory_state,
            &structured_input.observable_output.final_memory_state,
        )?;

    structured_input.hidden_fsm_output.precompile_state = final_state;
    structured_input.hidden_fsm_output.log_queue_state = final_requets_state;
    structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

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
