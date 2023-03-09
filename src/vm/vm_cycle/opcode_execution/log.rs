use super::*;
use zkevm_opcode_defs::definitions::log::*;
// use crate::vm::supplementary_structs::rollback_witness_handler::RollbackHandlerMode;
// use super::supplementary_structs::storage::*;
use super::super::primitives::{UInt16, UInt32, UInt64};
use crate::scheduler::queues::storage_log::*;
use crate::scheduler::queues::StorageLogQueue;
use crate::traits::CSWitnessable;
use crate::vm::primitives::register_view::Register;
use crate::vm::vm_state::*;
use zkevm_opcode_defs::FIRST_MESSAGE_FLAG_IDX;

// Log is currently a generalization of four types of operations.
// 1) storage load/store: [contract_address | key | read_value | written_value | rw_flag | shard_id]
// 2) event emission: [event_emitter_addr | field0 | field1 | is_init_event]
// 3) L1 event (publishing data onchain) [event_emitter_addr | field0 | field1 | is_init_event]
// 4) Precompile log [precompile_address| key: (input_args_page | input_offset | output_args_page | output_offet)]
// all of these logs are mapped to the following structure:
// pub struct StorageLogRecord<E: Engine> {
//     pub address: UInt160<E>,
//     pub key: UInt256<E>,
//     pub read_value: UInt256<E>,
//     pub written_value: UInt256<E>,
//     pub r_w_flag: Boolean,
//     pub aux_byte: Byte<E>,
//     pub rollback: Boolean,
//     pub is_service: Boolean,
//     pub shard_id: Byte<E>,
//     pub tx_number_in_block: UInt16<E>,
//     pub timestamp: UInt32<E>
// }

pub const STORAGE_AUX_BYTE: u8 = 0;
pub const EVENT_AUX_BYTE: u8 = 1;
pub const ONCHAIN_DATA_STORE_AUX_BYTE: u8 = 2;
pub const PRECOMPILE_AUX_BYTE: u8 = 3;

fn construct_hash_relations_for_log_and_new_queue_states<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    packed_log: LogRecordPackExtended<E>,
    forward_queue_tail: Num<E>,
    claimed_rollback_head: Num<E>,
    current_rollback_head: Num<E>,
    // current_rollback_tail: Num<E>,
    should_execute_either: &Boolean,
    should_execute_rollback: &Boolean,
    round_function: &R,
) -> Result<(Num<E>, Num<E>, Vec<PendingRecord<E, 3>>), SynthesisError> {
    const SWIDTH: usize = 3;
    const AWIDTH: usize = 2;

    // we should be clever and simultaneously produce 2 relations:
    // - 2 common sponges for forward/rollback that only touch the encodings
    // - 1 unique sponge for forward
    // - 1 unique sponge for rollback

    for i in 0..4 {
        assert!(packed_log.direct[i].eq(&packed_log.revert[i]));
    }

    let common_part: [Num<E>; 4] = packed_log.direct[0..4].try_into().unwrap();
    let mut it = common_part.chunks_exact(AWIDTH);

    let mut relations: Vec<PendingRecord<E, 3>> = Vec::with_capacity(4);

    let num_common_rounds = common_part.len() / AWIDTH;
    assert!(common_part.len() % AWIDTH == 0);

    let full_encoding_length = packed_log.direct.len() + 1;
    assert!(full_encoding_length % AWIDTH == 0);

    // now perform multiround absorbing by providing witness for round function output,
    // but perform absorbtion in the enforcable manner
    let mut current_state = R::empty_state();
    current_state = round_function.apply_length_specialization(current_state, full_encoding_length);

    for round_idx in 0..num_common_rounds {
        let chunk = it.next().unwrap();
        let mut provably_absorbed = current_state;

        if round_idx == 0 {
            // just set
            for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(chunk.iter()) {
                *dst = *src;
            }
        } else {
            // absorb by addition
            for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(chunk.iter()) {
                *dst = dst.add(cs, src)?;
            }
        }

        let round_function_output_witness = match Num::get_value_multiple(&provably_absorbed) {
            Some(provably_absorbed) => {
                if should_execute_either.get_value().unwrap_or(false) {
                    Some(round_function.simulate_round_function(provably_absorbed))
                } else {
                    Some([E::Fr::zero(); SWIDTH])
                }
            }
            _ => None,
        };
        let intermediate_candidate = Num::alloc_multiple(cs, round_function_output_witness)?;

        let new_relation = PendingRecord {
            initial_state: provably_absorbed,
            final_state: intermediate_candidate.clone(),
            is_used: should_execute_either.clone(),
        };
        relations.push(new_relation);

        current_state = intermediate_candidate;
    }

    let common_state = current_state;

    // now two uncommon relations
    let uncommon_forward: [Num<E>; AWIDTH] = packed_log.direct[4..]
        .iter()
        .copied()
        .chain(iter::once(forward_queue_tail))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let uncommon_rollback: [Num<E>; AWIDTH] = packed_log.revert[4..]
        .iter()
        .copied()
        .chain(iter::once(claimed_rollback_head))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    // -------------------------- forward ------------------------

    let mut provably_absorbed_forward = common_state;
    // absorb by addition
    for (dst, src) in provably_absorbed_forward[..AWIDTH]
        .iter_mut()
        .zip(uncommon_forward.into_iter())
    {
        *dst = dst.add(cs, &src)?;
    }

    let round_function_output_witness = match Num::get_value_multiple(&provably_absorbed_forward) {
        Some(provably_absorbed_forward) => {
            if should_execute_either.get_value().unwrap_or(false) {
                Some(round_function.simulate_round_function(provably_absorbed_forward))
            } else {
                Some([E::Fr::zero(); SWIDTH])
            }
        }
        _ => None,
    };

    let forward_final_state = Num::alloc_multiple(cs, round_function_output_witness)?;
    let forward_tail_candidate = R::state_into_commitment(forward_final_state)?;

    let new_relation = PendingRecord {
        initial_state: provably_absorbed_forward,
        final_state: forward_final_state,
        is_used: should_execute_either.clone(),
    };
    relations.push(new_relation);

    let new_forward_queue_tail = Num::conditionally_select(
        cs,
        &should_execute_either,
        &forward_tail_candidate,
        &forward_queue_tail,
    )?;

    // --------------- rollback --------------------

    let mut provably_absorbed_rollback = common_state;
    // absorb by addition
    for (dst, src) in provably_absorbed_rollback[..AWIDTH]
        .iter_mut()
        .zip(uncommon_rollback.into_iter())
    {
        *dst = dst.add(cs, &src)?;
    }

    let round_function_output_witness = match Num::get_value_multiple(&provably_absorbed_rollback) {
        Some(provably_absorbed_rollback) => {
            if should_execute_rollback.get_value().unwrap_or(false) {
                Some(round_function.simulate_round_function(provably_absorbed_rollback))
            } else {
                Some([E::Fr::zero(); SWIDTH])
            }
        }
        _ => None,
    };

    let rollback_final_state = Num::alloc_multiple(cs, round_function_output_witness)?;
    let presumably_current_rollback_head = R::state_into_commitment(rollback_final_state)?;

    let new_relation = PendingRecord {
        initial_state: provably_absorbed_rollback,
        final_state: rollback_final_state,
        is_used: should_execute_rollback.clone(),
    };
    relations.push(new_relation);

    let new_rollback_queue_head = Num::conditionally_select(
        cs,
        &should_execute_rollback,
        &claimed_rollback_head,
        &current_rollback_head,
    )?;

    Num::conditionally_enforce_equal(
        cs,
        should_execute_rollback,
        &current_rollback_head,
        &presumably_current_rollback_head,
    )?;

    Ok((new_forward_queue_tail, new_rollback_queue_head, relations))
}

pub(crate) fn apply<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    opcode_carry_parts: &OpcodeCarryParts<E>,
    _global_context: &GlobalContext<E>,
    optimizer: &mut OptimizationContext<E>,
    round_function: &R,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<OpcodePartialApplicationResult<E, PropsMarker>, SynthesisError> {
    let n = cs.get_current_aux_gate_number();

    let storage_read_opcode = zkevm_opcode_defs::Opcode::Log(LogOpcode::StorageRead);
    let storage_write_opcode = zkevm_opcode_defs::Opcode::Log(LogOpcode::StorageWrite);
    let to_l1_message_opcode = zkevm_opcode_defs::Opcode::Log(LogOpcode::ToL1Message);
    let event_opcode = zkevm_opcode_defs::Opcode::Log(LogOpcode::Event);
    let precompile_call_opcode = zkevm_opcode_defs::Opcode::Log(LogOpcode::PrecompileCall);

    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(event_opcode);

    let marker = CtxMarker::from(event_opcode);
    let shifts = compute_shifts::<E::Fr>();

    let is_storage_read = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(storage_read_opcode)
    };
    let is_storage_write = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(storage_write_opcode)
    };
    let is_event = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(event_opcode)
    };
    let is_l1_message = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(to_l1_message_opcode)
    };
    let is_precompile = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(precompile_call_opcode)
    };

    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing LOG");
        if is_storage_read.get_value().unwrap_or(false) {
            println!("Storage read");
        }
        if is_storage_write.get_value().unwrap_or(false) {
            println!("Storage write");
        }
        if is_event.get_value().unwrap_or(false) {
            println!("Event");
        }
        if is_l1_message.get_value().unwrap_or(false) {
            println!("To L1 message");
        }
        if is_precompile.get_value().unwrap_or(false) {
            println!("Precompile call");
        }
    }

    let address = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .this
        .clone();
    let key = UInt256 {
        inner: common_opcode_state.src0_view.u64x4_view.unwrap().clone(),
    };
    let written_value = UInt256 {
        inner: common_opcode_state.src1_view.u64x4_view.unwrap().clone(),
    };

    let key_for_precompile_call = {
        // Implement PrecompileCallABI parsing
        let memory_page_to_read = opcode_carry_parts.heap_page;

        // repack as PrecompileCallInnerABI. In fact it only replaces u64x4_view[2]
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&memory_page_to_read.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&opcode_carry_parts.heap_page.inner, shifts[32]); // heap
        let packed_word_2 = UInt64::from_num_unchecked(lc.into_num(cs)?);

        let mut result = key;
        result.inner[2] = packed_word_2;

        result
    };

    use zkevm_opcode_defs::system_params::{
        INITIAL_STORAGE_WRITE_PUBDATA_BYTES, L1_MESSAGE_PUBDATA_BYTES,
    };

    let is_rollup = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .this_shard_id
        .inner
        .is_zero(cs)?;
    let write_to_rollup = smart_and(cs, &[is_rollup, is_storage_write])?;

    let emit_l1_message = is_l1_message;
    let ergs_to_burn_for_l1_message = current_state.ergs_per_pubdata_byte.inner.mul(
        cs,
        &UInt32::from_uint(L1_MESSAGE_PUBDATA_BYTES as u32).inner,
    )?;
    let ergs_to_burn_for_l1_message = UInt32::from_num_unchecked(ergs_to_burn_for_l1_message);
    let ergs_to_burn_for_precompile_call = common_opcode_state.src1_view.u32x8_view.unwrap()[0];

    let is_storage_access = Boolean::or(cs, &is_storage_read, &is_storage_write)?;
    let is_nonrevertable = Boolean::or(cs, &is_storage_read, &is_precompile)?;
    let is_revertable = is_nonrevertable.not();

    let key = UInt256::conditionally_select(cs, &is_precompile, &key_for_precompile_call, &key)?;
    let written_value =
        UInt256::conditionally_select(cs, &is_precompile, &UInt256::zero(), &written_value)?;

    // this is actually a linear combination
    let mut lc = LinearCombination::zero();
    for (flag, value) in [
        (is_storage_access, STORAGE_AUX_BYTE),
        (is_event, EVENT_AUX_BYTE),
        (is_l1_message, ONCHAIN_DATA_STORE_AUX_BYTE),
        (is_precompile, PRECOMPILE_AUX_BYTE),
    ]
    .into_iter()
    {
        lc.add_assign_boolean_with_coeff(&flag, u64_to_fe(value as u64));
    }

    let aux_byte_as_u8 = UInt8::from_num_unchecked(lc.into_num(cs)?);

    let aux_byte = Byte {
        inner: aux_byte_as_u8.inner.clone(),
    };
    let timestamp = common_opcode_state.timestamp_for_first_decommit_or_precompile_read;
    let shard_id = Byte {
        inner: current_state
            .callstack
            .current_context
            .saved_context
            .common_part
            .this_shard_id
            .inner
            .clone(),
    };
    // NOTE: our opcodes encoding guarantees that there is no "storage read + is first"
    // variant encodable
    let is_event_init = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .flag_booleans[FIRST_MESSAGE_FLAG_IDX]
    };

    let mut log = StorageLogRecord {
        address,
        key,
        read_value: UInt256::zero(),
        written_value,
        r_w_flag: is_revertable,
        aux_byte,
        rollback: Boolean::constant(false),
        is_service: is_event_init,
        shard_id,
        tx_number_in_block: current_state.tx_number_in_block.clone(),
        timestamp,
    };

    // also we can push witness and get refund values
    let pubdata_refund_witness = witness_oracle.get_refunds(&log, &is_storage_write, &should_apply);
    let pubdata_refund = UInt32::allocate(cs, pubdata_refund_witness)?;

    // operator is not allowed to refund too much
    let (net_cost, uf) = UInt32::from_uint(INITIAL_STORAGE_WRITE_PUBDATA_BYTES as u32)
        .sub_using_delayed_bool_allocation(cs, &pubdata_refund, optimizer)?;
    Boolean::enforce_equal(cs, &uf, &Boolean::constant(false))?;

    let ergs_to_burn_for_rollup_storage_write = current_state
        .ergs_per_pubdata_byte
        .inner
        .mul(cs, &net_cost.inner)?;
    let ergs_to_burn_for_rollup_storage_write =
        UInt32::from_num_unchecked(ergs_to_burn_for_rollup_storage_write);

    // now we know net cost
    let ergs_to_burn = UInt32::conditionally_select(
        cs,
        &write_to_rollup,
        &ergs_to_burn_for_rollup_storage_write,
        &UInt32::zero(),
    )?;
    let ergs_to_burn = UInt32::conditionally_select(
        cs,
        &is_precompile,
        &ergs_to_burn_for_precompile_call,
        &ergs_to_burn,
    )?;
    let ergs_to_burn = UInt32::conditionally_select(
        cs,
        &emit_l1_message,
        &ergs_to_burn_for_l1_message,
        &ergs_to_burn,
    )?;

    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!(
            "Burning {} ergs as part of LOG",
            ergs_to_burn.get_value().unwrap()
        );
    }

    let (ergs_remaining, uf) = opcode_carry_parts
        .preliminary_ergs_left
        .sub_using_delayed_bool_allocation(cs, &ergs_to_burn, optimizer)?;
    let not_enough_ergs_for_op = uf;

    // if not enough then leave only 0
    let ergs_remaining = ergs_remaining.mask(cs, &not_enough_ergs_for_op.not())?;

    let execute_either_in_practice = smart_and(cs, &[should_apply, not_enough_ergs_for_op.not()])?;

    // we always access witness, as even for writes we have to get a claimed read value!
    let read_value_witness = witness_oracle.get_storage_read_witness(
        &log,
        &is_storage_access,
        &execute_either_in_practice,
    );

    let read_value = UInt256::allocate_in_optimization_context_with_applicability(
        cs,
        read_value_witness,
        optimizer,
        should_apply,
        marker,
    )?;

    let read_value =
        UInt256::conditionally_select(cs, &is_storage_access, &read_value, &UInt256::zero())?;
    log.read_value = read_value.clone();
    // if we read then use the same value - convension!
    log.written_value =
        UInt256::conditionally_select(cs, &log.r_w_flag, &log.written_value, &log.read_value)?;

    let packed_log = log.pack_extended(cs)?;

    let execute_rollback = smart_and(cs, &[execute_either_in_practice, is_revertable])?;

    let current_forward_tail = current_state
        .callstack
        .current_context
        .log_queue_forward_tail
        .clone();
    let current_rollback_head = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .reverted_queue_head
        .clone();
    let prev_revert_head_witness =
        witness_oracle.get_rollback_queue_witness(&log, &execute_rollback);

    let prev_revert_head_witness =
        Num::Variable(AllocatedNum::alloc(cs, || prev_revert_head_witness.grab())?);

    let (new_forward_queue_tail, new_rollback_queue_head, relations) =
        construct_hash_relations_for_log_and_new_queue_states(
            cs,
            packed_log,
            current_forward_tail,
            prev_revert_head_witness,
            current_rollback_head,
            &execute_either_in_practice,
            &execute_rollback,
            round_function,
        )?;

    // add actual update of register in case of write
    let read_value_chunk0 = {
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&read_value.inner[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&read_value.inner[1].inner, shifts[64]);
        UInt128::from_num_unchecked(lc.into_num(cs)?)
    };
    let read_value_chunk1 = {
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&read_value.inner[2].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&read_value.inner[3].inner, shifts[64]);
        UInt128::from_num_unchecked(lc.into_num(cs)?)
    };
    let register_if_storage_read = Register {
        inner: [read_value_chunk0, read_value_chunk1],
        is_ptr: Boolean::Constant(false),
    };
    // precompile call result
    let mut lc = LinearCombination::zero();
    // return 1 if we are successfully burned and called precompile, and 0 otherwise
    lc.add_assign_boolean_with_coeff(&not_enough_ergs_for_op.not(), E::Fr::one());
    let reg_low = UInt128::from_num_unchecked(lc.into_num(cs)?);
    let register_if_precompile_call = Register {
        inner: [reg_low, UInt128::zero()],
        is_ptr: Boolean::Constant(false),
    };

    let register = Register::conditionally_select(
        cs,
        &is_storage_read,
        &register_if_storage_read,
        &register_if_precompile_call,
    )?;

    let old_forward_queue_length = current_state
        .callstack
        .current_context
        .log_queue_forward_part_length
        .clone();
    let new_forward_queue_length = old_forward_queue_length
        .conditionally_increment_unchecked(cs, &execute_either_in_practice)?;

    let old_revert_queue_length = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .reverted_queue_segment_len
        .clone();
    let new_revert_queue_length =
        old_revert_queue_length.conditionally_increment_unchecked(cs, &execute_rollback)?;

    // we use 3 sponges for forward and 1 extra for rollback
    assert_eq!(relations.len(), 4);

    let can_update_dst0 = smart_or(cs, &[is_storage_read, is_precompile])?;
    let should_update_dst0 = smart_and(cs, &[can_update_dst0, should_apply])?;

    let mut result = OpcodePartialApplicationResult::default();
    result.marker = PropsMarker::Normal(storage_read_opcode);
    result.applies = should_apply;
    result.pending_sponges = relations;
    result.dst0_value = Some((should_update_dst0, register));
    result.new_forward_queue_state = Some(new_forward_queue_tail);
    result.new_forward_queue_length = Some(new_forward_queue_length);
    result.new_rollback_queue_state = Some(new_rollback_queue_head);
    result.new_rollback_queue_length = Some(new_revert_queue_length);
    result.ergs_left = Some(ergs_remaining);

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!(
        "{} gates used for opcode {:?}",
        gates_used, storage_read_opcode
    );
    // dbg!(_message);

    Ok(result)
}
