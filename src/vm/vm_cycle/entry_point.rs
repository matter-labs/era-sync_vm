use zkevm_opcode_defs::system_params::BOOTLOADER_FORMAL_ADDRESS_LOW;
use zkevm_opcode_defs::FatPointer;

use super::*;

use crate::glue::optimizable_queue::commit_variable_length_encodable_item;
use crate::inputs::ClosedFormInputCompactForm;
use crate::scheduler::queues::FullSpongeLikeQueueState;
use crate::traits::*;
use crate::vm::primitives::register_view::Register;
use crate::vm::vm_cycle::input::*;
use crate::vm::vm_cycle::witness_oracle::WitnessOracle;
use crate::vm::vm_state::VmGlobalState;

pub fn vm_circuit_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    W: WitnessOracle<E>,
>(
    cs: &mut CS,
    witness: Option<VmCircuitWitness<E, W>>,
    round_function: &R,
    limit: usize,
) -> Result<AllocatedNum<E>, SynthesisError> {
    add_all_tables(cs)?;

    let (structured_input_witness, witness_oracle) = match witness {
        Some(w) => {
            let VmCircuitWitness {
                closed_form_input,
                witness_oracle,
            } = w;

            (Some(closed_form_input), Some(witness_oracle))
        }
        None => (None, None),
    };

    let mut structured_input =
        VmCircuitInputOutput::alloc_ignoring_outputs(cs, structured_input_witness.clone())?;

    let start_flag = structured_input.start_flag;
    let observable_input = structured_input.observable_input.clone();
    let hidden_fsm_input = structured_input.hidden_fsm_input.clone();

    let VmInputData {
        rollback_queue_tail_for_block,
        memory_queue_initial_state,
        decommitment_queue_initial_state,
        per_block_context,
    } = observable_input;

    // we also need to create the state that reflects the "initial" state for boot process

    let bootloader_state = initial_state_for_bootloading(
        cs,
        memory_queue_initial_state,
        decommitment_queue_initial_state,
        rollback_queue_tail_for_block,
        round_function,
    )?;

    // or may be it's from FSM, so select
    let initial_state =
        VmGlobalState::conditionally_select(cs, &start_flag, &bootloader_state, &hidden_fsm_input)?;

    let mut expanded_state: VmLocalState<E, 3> = initial_state.into();

    if crate::VERBOSE_CIRCUITS {
        if let Some(default_aa) = per_block_context.default_aa_code_hash.get_value() {
            println!("Default AA = 0x{:064x}", default_aa);
        }
    }

    let mut oracle = witness_oracle.unwrap_or_default();

    use crate::vm::vm_cycle::cycle::vm_cycle;
    use crate::vm::vm_cycle::cycle::vm_process_pending;

    // we run `limit` of "normal" cycles
    for _ in 0..limit {
        let n = cs.get_current_aux_gate_number();

        expanded_state = vm_cycle(
            cs,
            expanded_state,
            &mut oracle,
            round_function,
            &per_block_context,
        )?;
        let _used_gates_per_cycle = cs.get_current_aux_gate_number() - n;
        // dbg!(_used_gates_per_cycle);
    }

    // and at most 1 to process pending and only in this case
    let final_state_no_pending = vm_process_pending(cs, expanded_state, round_function)?;

    // here we have too large state to run self-tests, so we will compare it only against the full committments

    // check for "done" flag
    let done = final_state_no_pending.callstack.is_empty(cs)?;

    // we can not fail exiting, so check for our convention that pc == 0 on success, and != 0 in failure
    let bootloader_exited_successfully = final_state_no_pending
        .callstack
        .current_context
        .saved_context
        .common_part
        .pc
        .is_zero(cs)?;
    can_not_be_false_if_flagged(cs, &bootloader_exited_successfully, &done)?;

    structured_input.completion_flag = done;

    let mut observable_output = VmOutputData::empty();
    // memory
    observable_output.memory_queue_final_state.tail = <[Num<E>; 3]>::conditionally_select(
        cs,
        &structured_input.completion_flag,
        &final_state_no_pending.memory_queue_state,
        &observable_output.memory_queue_final_state.tail,
    )?;
    observable_output.memory_queue_final_state.length = UInt32::conditionally_select(
        cs,
        &structured_input.completion_flag,
        &final_state_no_pending.memory_queue_length,
        &observable_output.memory_queue_final_state.length,
    )?;

    // code decommit
    observable_output.decommitment_queue_final_state.tail = <[Num<E>; 3]>::conditionally_select(
        cs,
        &structured_input.completion_flag,
        &final_state_no_pending.code_decommittment_queue_state,
        &observable_output.decommitment_queue_final_state.tail,
    )?;
    observable_output.decommitment_queue_final_state.length = UInt32::conditionally_select(
        cs,
        &structured_input.completion_flag,
        &final_state_no_pending.code_decommittment_queue_length,
        &observable_output.decommitment_queue_final_state.length,
    )?;

    // log. We IGNORE rollbacks that never happened obviously
    let final_log_state_tail = final_state_no_pending
        .callstack
        .current_context
        .log_queue_forward_tail;
    let final_log_state_length = final_state_no_pending
        .callstack
        .current_context
        .log_queue_forward_part_length;

    // but we CAN still check that it's potentially mergeable, basically to check that witness generation is good
    Num::conditionally_enforce_equal(
        cs,
        &structured_input.completion_flag,
        &final_log_state_tail,
        &final_state_no_pending
            .callstack
            .current_context
            .saved_context
            .common_part
            .reverted_queue_head,
    )?;

    observable_output.log_queue_final_state.tail_state = Num::conditionally_select(
        cs,
        &structured_input.completion_flag,
        &final_log_state_tail,
        &observable_output.log_queue_final_state.tail_state,
    )?;
    observable_output.log_queue_final_state.num_items = UInt32::conditionally_select(
        cs,
        &structured_input.completion_flag,
        &final_log_state_length,
        &observable_output.log_queue_final_state.num_items,
    )?;

    structured_input.observable_output = observable_output;
    structured_input.hidden_fsm_output = final_state_no_pending;

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = structured_input_witness {
            assert_eq!(circuit_result, passed_input);
        }
    }

    // we short-circuit self-checks at setup by checking if witness was generated at all
    if structured_input.completion_flag.get_value().is_some() {
        oracle.at_completion();
    }

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    // dbg!(compact_form.create_witness());
    use crate::glue::optimizable_queue::commit_encodable_item;

    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();

    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;
    // dbg!(input_committment_value);

    Ok(public_input)
}

use crate::vm::primitives::*;
use crate::vm::vm_state::execution_context::FullExecutionContext;
use crate::vm::vm_state::VmLocalState;

pub fn initial_state_for_bootloading<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    memory_queue_initial_state: FullSpongeLikeQueueState<E>,
    decommitment_queue_initial_state: FullSpongeLikeQueueState<E>,
    initial_rollback_queue_value: Num<E>,
    round_function: &R,
) -> Result<VmGlobalState<E, 3>, SynthesisError> {
    // first create the context
    let mut ctx = FullExecutionContext::uninitialized();

    ctx.saved_context.common_part.base_page =
        UInt32::from_uint(zkevm_opcode_defs::BOOTLOADER_BASE_PAGE);
    ctx.saved_context.common_part.code_page =
        UInt32::from_uint(zkevm_opcode_defs::BOOTLOADER_CODE_PAGE);

    ctx.saved_context.common_part.pc = UInt16::zero();
    ctx.saved_context.common_part.exception_handler_loc =
        UInt16::from_uint(zkevm_opcode_defs::system_params::INITIAL_FRAME_FORMAL_EH_LOCATION);
    ctx.saved_context.common_part.ergs_remaining =
        UInt32::from_uint(zkevm_opcode_defs::system_params::VM_INITIAL_FRAME_ERGS);

    let formal_bootloader_address =
        u160::from_u64(zkevm_opcode_defs::system_params::BOOTLOADER_FORMAL_ADDRESS_LOW as u64);

    ctx.saved_context.common_part.code_address = UInt160::from_uint(formal_bootloader_address);
    ctx.saved_context.common_part.this = UInt160::from_uint(formal_bootloader_address);
    ctx.saved_context.common_part.caller = UInt160::zero(); // is called from nowhere

    // circuit specific bit
    ctx.saved_context.common_part.reverted_queue_tail = initial_rollback_queue_value;
    ctx.saved_context.common_part.reverted_queue_head =
        ctx.saved_context.common_part.reverted_queue_tail;

    // mark as kernel
    ctx.saved_context.common_part.is_kernel_mode = Boolean::constant(true);

    // bootloader should not pay for resizes
    ctx.saved_context.common_part.heap_upper_bound =
        UInt32::from_uint(zkevm_opcode_defs::system_params::BOOTLOADER_MAX_MEMORY);
    ctx.saved_context.common_part.aux_heap_upper_bound =
        UInt32::from_uint(zkevm_opcode_defs::system_params::BOOTLOADER_MAX_MEMORY);

    // now push that to the callstack, manually

    let mut empty_entry = FullExecutionContext::uninitialized();
    empty_entry.saved_context.common_part.reverted_queue_tail = initial_rollback_queue_value;
    empty_entry.saved_context.common_part.reverted_queue_head =
        ctx.saved_context.common_part.reverted_queue_tail;
    empty_entry.saved_context.common_part.is_kernel_mode = Boolean::constant(true);

    let empty_entry_encoding = empty_entry.saved_context.pack(cs)?; // only saved part
    let callstack_initial_state = round_function.round_function_absorb_nums_multiple_rounds(
        cs,
        [Num::zero(); 3],
        &empty_entry_encoding,
    )?;
    let callstack_depth = UInt32::<E>::from_uint(1u32);

    use crate::vm::vm_state::callstack::Callstack;

    let callstack = Callstack::<E, 3> {
        current_context: ctx,
        context_stack_depth: callstack_depth,
        stack_sponge_state: callstack_initial_state,
    };

    let mut bootloaded_state = VmGlobalState::empty();
    // memory
    bootloaded_state.memory_queue_length = memory_queue_initial_state.length;
    bootloaded_state.memory_queue_state = memory_queue_initial_state.tail;
    // code decommittments
    bootloaded_state.code_decommittment_queue_length = decommitment_queue_initial_state.length;
    bootloaded_state.code_decommittment_queue_state = decommitment_queue_initial_state.tail;
    // rest
    bootloaded_state.did_call_or_ret_recently = Boolean::constant(true); // we are just at the start
    bootloaded_state.callstack = callstack;
    // timestamp and global counters
    bootloaded_state.timestamp = UInt32::from_uint(zkevm_opcode_defs::STARTING_TIMESTAMP);
    bootloaded_state.memory_page_counter = UInt32::from_uint(zkevm_opcode_defs::STARTING_BASE_PAGE);

    // we also FORMALLY mark r1 as "pointer" type, even though we will NOT have any calldata
    // Nevertheless we put it "formally" to make an empty slice to designated page

    let formal_ptr = FatPointer {
        offset: 0,
        memory_page: zkevm_opcode_defs::BOOTLOADER_CALLDATA_PAGE,
        start: 0,
        length: 0,
    };
    let formal_ptr_encoding = formal_ptr.to_u256();
    bootloaded_state.registers[0] = Register {
        inner: [
            UInt128::from_uint(
                (formal_ptr_encoding.0[0] as u128) + ((formal_ptr_encoding.0[1] as u128) << 64),
            ),
            UInt128::zero(),
        ],
        is_ptr: Boolean::Constant(true),
    };

    Ok(bootloaded_state)
}
