use super::*;
use crate::vm::primitives::register_view::Register;
use crate::vm::vm_cycle::memory::may_be_write_memory;
use crate::vm::vm_cycle::opcode_bitmask::SUPPORTED_ISA_VERSION;
use crate::vm::vm_cycle::pre_state::*;
use crate::vm::vm_cycle::witness_oracle::WitnessOracle;
use crate::vm::vm_state::*;
use zkevm_opcode_defs::Opcode;

use zkevm_opcode_defs::system_params::NUM_SPONGES;
use zkevm_opcode_defs::MAX_PENDING_CYCLES;

pub fn merge_into_next_state<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: VmLocalState<E, 3>,
    carried_info: OpcodeCarryParts<E>,
    opcode_results: Vec<OpcodePartialApplicationResult<E, PropsMarker>>,
    round_function: &R,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<VmLocalState<E, 3>, SynthesisError> {
    let OpcodeCarryParts {
        did_skip_cycle,
        opcode_read_sponge_data,
        src0_read_sponge_data,
        decoded_opcode,
        dst0_memory_location,
        dst0_performs_memory_access,
        timestamp_for_code_or_src_read: _,
        timestamp_for_first_decommit_or_precompile_read: _,
        timestamp_for_second_decommit_or_precompile_write: _,
        timestamp_for_dst_write,
        next_cycle_timestamp,
        preliminary_ergs_left,
        pc_plus_one,
        heap_page: _,
        aux_heap_page: _,
    } = carried_info;

    let mut new_state = current_state;

    // sort the opcodes results
    let opcode_results = opcode_results;
    let mut applicability_flags = vec![];
    for result in opcode_results.iter() {
        applicability_flags.push(result.applies);
    }

    let it = applicability_flags
        .iter()
        .copied()
        .zip(opcode_results.iter());

    // combine the information from the definitions whether we will update or not dst0 IN MEMORY
    let mut write_dst0_bools = vec![];
    for (applies, application_result) in it.clone() {
        if application_result
            .marker
            .can_write_dst0_into_memory(SUPPORTED_ISA_VERSION)
        {
            write_dst0_bools.push(applies);
        }
    }
    let should_write_memory_for_dst0 = smart_or(cs, &write_dst0_bools)?;

    // select dst0 and dst1 values
    let mut dst0_candidates = vec![];
    let mut should_update_dst0 = vec![];
    let mut dst1_candidates = vec![];
    let mut should_update_dst1 = vec![];
    for (_opcode_applies, application_result) in it.clone() {
        // src 0 may or may not be updated
        if let Some((applies, dst0)) = application_result.dst0_value.as_ref() {
            dst0_candidates.push((*applies, dst0.clone()));
            should_update_dst0.push(*applies);
        }
        if let Some((applies, dst1)) = application_result.dst1_value.as_ref() {
            dst1_candidates.push((*applies, dst1.clone()));
            should_update_dst1.push(*applies);
        }
    }

    assert!(
        should_update_dst0
            .iter()
            .filter(|x| x.get_value().unwrap_or(false))
            .count()
            <= 1
    );
    assert!(
        should_update_dst1
            .iter()
            .filter(|x| x.get_value().unwrap_or(false))
            .count()
            <= 1
    );

    let should_update_dst0 = smart_or(cs, &should_update_dst0)?;
    let should_update_dst1 = smart_or(cs, &should_update_dst1)?;

    let mut drain = dst0_candidates.drain(..);
    let (_, mut dst0) = drain.next().unwrap();
    for (apply, candidate) in drain {
        dst0 = Register::conditionally_select(cs, &apply, &candidate, &dst0)?;
    }

    let mut drain = dst1_candidates.drain(..);
    let (_, mut dst1) = drain.next().unwrap();
    for (apply, candidate) in drain {
        dst1 = Register::conditionally_select(cs, &apply, &candidate, &dst1)?;
    }

    let perform_dst0_memory_write_update = smart_and(
        cs,
        &[
            should_update_dst0,
            should_write_memory_for_dst0,
            dst0_performs_memory_access,
        ],
    )?;

    // resolve sponge chains
    // for it we do the following logical reduction
    // - for every opcode we make a chain of how many sponges is COULD potentially use in a worst case (including code read!)
    // - then chunk it over sponges per cycle
    // - then using "did_skip_cycle" we additionally mask out this cycle POTENTIAL results (since we formally would execute NOP)
    // - so we get proper sets

    // we already have internal boolean marker whether it should use it
    let first_sponge_for_code_read = opcode_read_sponge_data;
    let second_sponge_for_src0 = src0_read_sponge_data;
    let third_sponge_for_dst0 = {
        let (
            initial_state_sponge_3,
            final_state_sponge_3,
            new_memory_queue_length,
            should_use_sponge_3,
        ) = may_be_write_memory(
            cs,
            perform_dst0_memory_write_update,
            dst0.clone(),
            timestamp_for_dst_write,
            dst0_memory_location,
            new_state.memory_queue_state,
            new_state.memory_queue_length,
            round_function,
            witness_oracle,
        )?;

        new_state.memory_queue_state = final_state_sponge_3;
        new_state.memory_queue_length = new_memory_queue_length;

        PendingRecord {
            initial_state: initial_state_sponge_3,
            final_state: final_state_sponge_3,
            is_used: should_use_sponge_3,
        }
    };

    // perform DST updates for non-specific registers
    let dst0_is_in_register = decoded_opcode
        .properties_bits
        .boolean_for_dst_mem_access(zkevm_opcode_defs::ImmMemHandlerFlags::UseRegOnly);
    let should_update_dst0_register = smart_and(cs, &[should_update_dst0, dst0_is_in_register])?;

    for (idx, marker) in decoded_opcode.dst_regs_selectors[0].iter().enumerate() {
        let update_this = smart_and(cs, &[should_update_dst0_register, *marker])?;
        new_state.registers[idx] =
            Register::conditionally_select(cs, &update_this, &dst0, &new_state.registers[idx])?;
    }

    for (idx, marker) in decoded_opcode.dst_regs_selectors[1].iter().enumerate() {
        let update_this = smart_and(cs, &[should_update_dst1, *marker])?;
        new_state.registers[idx] =
            Register::conditionally_select(cs, &update_this, &dst1, &new_state.registers[idx])?;
    }

    // now resolve more opcode-specific parts

    // special register updates. Use separate marker for it!
    for (_applies, application_result) in it.clone() {
        for (reg_idx, should_update, new_value) in
            application_result.specific_registers_updates.iter()
        {
            new_state.registers[*reg_idx] = Register::conditionally_select(
                cs,
                should_update,
                new_value,
                &new_state.registers[*reg_idx],
            )?;
        }
    }

    // zero out registers
    for (_applies, application_result) in it.clone() {
        for (should_update, reg_idx) in application_result.zero_out_specific_registers.iter() {
            new_state.registers[*reg_idx].inner = <[UInt128<E>; 2]>::conditionally_select(
                cs,
                should_update,
                &[UInt128::zero(); 2],
                &new_state.registers[*reg_idx].inner,
            )?;
        }
    }

    // remove ptr markers
    for (_applies, application_result) in it.clone() {
        for (should_update, reg_idx) in application_result.remove_ptr_on_specific_registers.iter() {
            new_state.registers[*reg_idx].is_ptr = Boolean::conditionally_select(
                cs,
                should_update,
                &Boolean::constant(false),
                &new_state.registers[*reg_idx].is_ptr,
            )?;
        }
    }

    // update ergs left
    new_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .ergs_remaining = preliminary_ergs_left;
    for (applies, application_result) in it.clone() {
        if let Some(ergs_left) = application_result.ergs_left.as_ref() {
            new_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .ergs_remaining = UInt32::conditionally_select(
                cs,
                &applies,
                ergs_left,
                &new_state
                    .callstack
                    .current_context
                    .saved_context
                    .common_part
                    .ergs_remaining,
            )?;
        }
    }

    // update PC field that is NOT part of the callstack changes

    // do not advance if we did skip
    let new_pc = UInt16::conditionally_select(
        cs,
        &did_skip_cycle,
        &new_state
            .callstack
            .current_context
            .saved_context
            .common_part
            .pc,
        &pc_plus_one,
    )?;
    new_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .pc = new_pc;

    // now apply specific updates

    // pending exception
    for (applies, application_result) in it.clone() {
        if let Some(new_pending_exception) = application_result.pending_exception.as_ref() {
            new_state.pending_exception = Boolean::conditionally_select(
                cs,
                &applies,
                new_pending_exception,
                &new_state.pending_exception,
            )?;
        }
    }

    // PC
    for (applies, application_result) in it.clone() {
        if let Some(pc) = application_result.new_pc.as_ref() {
            new_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .pc = UInt16::conditionally_select(
                cs,
                &applies,
                pc,
                &new_state
                    .callstack
                    .current_context
                    .saved_context
                    .common_part
                    .pc,
            )?;
        }
    }

    // heap and aux heap resize
    for (_applies, application_result) in it.clone() {
        if let Some((apply, bound)) = application_result.new_heap_upper_bound.as_ref() {
            new_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .heap_upper_bound = UInt32::conditionally_select(
                cs,
                &apply,
                bound,
                &new_state
                    .callstack
                    .current_context
                    .saved_context
                    .common_part
                    .heap_upper_bound,
            )?;
        }

        if let Some((apply, bound)) = application_result.new_aux_heap_upper_bound.as_ref() {
            new_state
                .callstack
                .current_context
                .saved_context
                .common_part
                .aux_heap_upper_bound = UInt32::conditionally_select(
                cs,
                &apply,
                bound,
                &new_state
                    .callstack
                    .current_context
                    .saved_context
                    .common_part
                    .aux_heap_upper_bound,
            )?;
        }
    }

    // we also update storage log states as they are formally saved in callstack,
    // but LOG opcode may update a very small part of it

    for (applies, application_result) in it.clone() {
        match (
            application_result.new_forward_queue_state.as_ref(),
            application_result.new_forward_queue_length.as_ref(),
            application_result.new_rollback_queue_state.as_ref(),
            application_result.new_rollback_queue_length.as_ref(),
        ) {
            (
                Some(new_forward_queue_state),
                Some(new_forward_queue_length),
                Some(new_rollback_queue_state),
                Some(new_rollback_queue_length),
            ) => {
                new_state.callstack.current_context.log_queue_forward_tail =
                    Num::conditionally_select(
                        cs,
                        &applies,
                        &new_forward_queue_state,
                        &new_state.callstack.current_context.log_queue_forward_tail,
                    )?;

                new_state
                    .callstack
                    .current_context
                    .log_queue_forward_part_length = UInt32::conditionally_select(
                    cs,
                    &applies,
                    &new_forward_queue_length,
                    &new_state
                        .callstack
                        .current_context
                        .log_queue_forward_part_length,
                )?;

                new_state
                    .callstack
                    .current_context
                    .saved_context
                    .common_part
                    .reverted_queue_head = Num::conditionally_select(
                    cs,
                    &applies,
                    &new_rollback_queue_state,
                    &new_state
                        .callstack
                        .current_context
                        .saved_context
                        .common_part
                        .reverted_queue_head,
                )?;

                new_state
                    .callstack
                    .current_context
                    .saved_context
                    .common_part
                    .reverted_queue_segment_len = UInt32::conditionally_select(
                    cs,
                    &applies,
                    &new_rollback_queue_length,
                    &new_state
                        .callstack
                        .current_context
                        .saved_context
                        .common_part
                        .reverted_queue_segment_len,
                )?;
            }
            (None, None, None, None) => {}
            _ => unreachable!(),
        }
    }

    // and if opcode modifies callstack in full then we will immediatelly overwrite it anyway!
    for (applies, application_result) in it.clone() {
        use crate::vm::vm_state::callstack::Callstack;

        if let Some(callstack) = application_result.callstack.as_ref() {
            new_state.callstack =
                Callstack::conditionally_select(cs, &applies, callstack, &new_state.callstack)?;
        }
    }

    // all the changes below do NOT touch new_state.callstack

    // update decommittment queue
    for (_applies, application_result) in it.clone() {
        match (
            application_result.new_decommittment_queue_length.as_ref(),
            application_result.new_decommittment_queue_state.as_ref(),
        ) {
            (Some(new_decommittment_queue_length), Some(new_decommittment_queue_state)) => {
                let update_decommittment_queue = application_result
                    .update_decommittment_queue
                    .expect("must be present if we update code decommittment queues");
                new_state.code_decommittment_queue_state = <[Num<E>; 3]>::conditionally_select(
                    cs,
                    &update_decommittment_queue,
                    &new_decommittment_queue_state,
                    &new_state.code_decommittment_queue_state,
                )?;

                new_state.code_decommittment_queue_length = UInt32::conditionally_select(
                    cs,
                    &update_decommittment_queue,
                    &new_decommittment_queue_length,
                    &new_state.code_decommittment_queue_length,
                )?;
            }
            (None, None) => {}
            _ => unreachable!(),
        }
    }

    // update memory queue state. Those can only happen in opcodes that do NOT have dst addressable in memory,
    // namely - UMA only
    for (applies, application_result) in it.clone() {
        match (
            application_result.new_memory_queue_length.as_ref(),
            application_result.new_memory_queue_state.as_ref(),
        ) {
            (Some(new_memory_queue_length), Some(new_memory_queue_state)) => {
                new_state.memory_queue_state = <[Num<E>; 3]>::conditionally_select(
                    cs,
                    &applies,
                    new_memory_queue_state,
                    &new_state.memory_queue_state,
                )?;

                new_state.memory_queue_length = UInt32::conditionally_select(
                    cs,
                    &applies,
                    new_memory_queue_length,
                    &new_state.memory_queue_length,
                )?;
            }
            (None, None) => {}
            _ => unreachable!(),
        }
    }

    // update ergs per pubdata, tx index, recent call/ret marker
    for (applies, application_result) in it.clone() {
        if let Some((apply, tx_index)) = application_result.new_tx_number_in_block.as_ref() {
            new_state.tx_number_in_block =
                UInt16::conditionally_select(cs, &apply, tx_index, &new_state.tx_number_in_block)?;
        }
        if let Some((apply, ergs_per_pubdata_byte)) =
            application_result.new_ergs_per_pubdata_byte.as_ref()
        {
            new_state.ergs_per_pubdata_byte = UInt32::conditionally_select(
                cs,
                &apply,
                ergs_per_pubdata_byte,
                &new_state.ergs_per_pubdata_byte,
            )?;
        }

        // we pre-initialized it
        if let Some(did_call_or_ret_recently) =
            application_result.new_did_call_or_ret_recently.as_ref()
        {
            new_state.did_call_or_ret_recently = Boolean::conditionally_select(
                cs,
                &applies,
                did_call_or_ret_recently,
                &new_state.did_call_or_ret_recently,
            )?;
        }

        if let Some(new_memory_pages_counter) = application_result.new_memory_pages_counter.as_ref()
        {
            new_state.memory_page_counter = UInt32::conditionally_select(
                cs,
                &applies,
                new_memory_pages_counter,
                &new_state.memory_page_counter,
            )?;
        }

        if let Some((apply, new_context_u128_value)) =
            application_result.context_u128_new_value.as_ref()
        {
            for (dst, src) in new_state
                .context_composite_u128
                .iter_mut()
                .zip(new_context_u128_value.iter())
            {
                *dst = UInt64::conditionally_select(cs, apply, &src, &dst)?;
            }
        }
    }

    // now update flags
    // these change quite a lot potentially, so we partition as much as we can

    new_state.flags = select_flags(cs, &new_state.flags, it.clone())?;

    // so we are done with the simplest parts
    // and then resolve pending

    // sponge chains!

    let mut sponge_chains = vec![];
    // now up to 7 (num_sponges * (1 + max_pending_cycles) - 1) pending requests from different opcodes
    for (_applies, application_result) in it.clone() {
        let mut per_opcode_sponges = vec![];
        // always push code query
        per_opcode_sponges.push(first_sponge_for_code_read.clone());
        // may be opcode uses query for SRC0
        if application_result
            .marker
            .can_have_src0_from_mem(SUPPORTED_ISA_VERSION)
        {
            per_opcode_sponges.push(second_sponge_for_src0);
        }
        // may be opcode uses query for DST0
        if application_result
            .marker
            .can_write_dst0_into_memory(SUPPORTED_ISA_VERSION)
        {
            per_opcode_sponges.push(third_sponge_for_dst0);
        }

        per_opcode_sponges.extend_from_slice(&application_result.pending_sponges);
        assert!(per_opcode_sponges.len() <= NUM_SPONGES * (MAX_PENDING_CYCLES + 1));
        sponge_chains.push(per_opcode_sponges);
    }

    // we need to chunk into rounds - one to execute this cycle, and one to carry to the next one may be
    let (this_cycle_sponges, pending_sponges) =
        select_and_align_sponge_chains(cs, new_state.pending_sponges.records, sponge_chains)?;

    // run sponges!

    let n = cs.get_current_aux_gate_number();

    for (_request_idx, request) in this_cycle_sponges.into_iter().enumerate() {
        let PendingRecord {
            initial_state,
            final_state,
            is_used,
        } = request;

        let true_final_state = round_function.round_function(cs, initial_state)?;

        for (a, b) in final_state.into_iter().zip(true_final_state.into_iter()) {
            Num::conditionally_enforce_equal(cs, &is_used, &a, &b)?;
        }
    }

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for sponges", gates_used);
    // dbg!(_message);

    // update pending
    new_state.pending_sponges.records = pending_sponges;

    // update timestamp
    new_state.timestamp = next_cycle_timestamp;

    Ok(new_state)
}

pub fn select_and_align_sponge_chains<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    current_pending: [[PendingRecord<E, 3>; NUM_SPONGES]; MAX_PENDING_CYCLES],
    chains: Vec<Vec<PendingRecord<E, 3>>>,
) -> Result<
    (
        [PendingRecord<E, 3>; NUM_SPONGES],
        [[PendingRecord<E, 3>; NUM_SPONGES]; MAX_PENDING_CYCLES],
    ),
    SynthesisError,
> {
    // we have explicitly constructed the chains such that we have a lot of duplicates, so sort
    let mut any_pending = false;
    for row in current_pending.iter() {
        for el in row.iter() {
            if el.is_used.get_value().unwrap_or(false) {
                any_pending = true;
            }
        }
    }

    let mut chains = chains;
    let mut selection_results = vec![];
    // let mut current_pending_vec = vec![];
    // for row in current_pending.iter() {
    //     current_pending_vec.extend_from_slice(row);
    // }
    // let mut current_pending_it = current_pending_vec.drain(..);

    for _ in 0..(NUM_SPONGES * (MAX_PENDING_CYCLES + 1)) {
        let mut sub_partitions: Vec<(([Num<E>; 3], [Num<E>; 3]), Vec<Boolean>)> = vec![];
        // if let Some(from_current_pending) = current_pending_it.next() {
        //     let PendingRecord {
        //         initial_state,
        //         final_state,
        //         is_used,
        //     } = from_current_pending;
        //     sub_partitions.push(((initial_state, final_state), vec![is_used]));
        // }

        for per_opcode_chain in chains.iter_mut() {
            if per_opcode_chain.len() == 0 {
                continue;
            }
            if let Some(per_opcode_next) = per_opcode_chain.drain(..1).next() {
                // try to find partition id that we can use
                let mut found = false;
                let mut idx = 0;
                let mut boolean_flag = Boolean::constant(false);
                for (i, existing_partition) in sub_partitions.iter().enumerate() {
                    let ((initial_state, final_state), _) = &existing_partition;
                    if CircuitEq::eq(initial_state, &per_opcode_next.initial_state)
                        && CircuitEq::eq(final_state, &per_opcode_next.final_state)
                    {
                        idx = i;
                        boolean_flag = per_opcode_next.is_used;
                        found = true;
                        break;
                    }
                }

                if any_pending {
                    assert!(
                        boolean_flag.get_value().unwrap_or(false) == false,
                        "we have something pending from the previous cycle, and we try to add more"
                    );
                }

                if found {
                    sub_partitions[idx].1.push(boolean_flag);
                } else {
                    // create new partition
                    let PendingRecord {
                        initial_state,
                        final_state,
                        is_used,
                    } = per_opcode_next;
                    sub_partitions.push(((initial_state, final_state), vec![is_used]));
                }
            } else {
                unreachable!()
            }
        }

        let mut it = sub_partitions.drain(..);
        let ((mut result_initial, mut result_final), flags) = it.next().unwrap();
        let is_used = smart_or(cs, &flags)?;
        // dbg!(is_used.get_value());

        let mut usability_flags = vec![is_used];

        for ((candidate_initial, candidate_final), flags) in it {
            let candidate_used = smart_or(cs, &flags)?;
            usability_flags.push(candidate_used);

            result_initial = <[Num<E>; 3]>::conditionally_select(
                cs,
                &candidate_used,
                &candidate_initial,
                &result_initial,
            )?;

            result_final = <[Num<E>; 3]>::conditionally_select(
                cs,
                &candidate_used,
                &candidate_final,
                &result_final,
            )?;
        }

        let is_used = smart_or(cs, &usability_flags)?;

        let record = PendingRecord {
            initial_state: result_initial,
            final_state: result_final,
            is_used,
        };

        selection_results.push(record);
    }

    // now just chunk

    let mut it = selection_results.chunks_exact(NUM_SPONGES);
    let this_cycle: [_; NUM_SPONGES] = it.next().unwrap().try_into().unwrap();

    let mut next_cycles = vec![];
    for chunk in &mut it {
        let cycle: [_; NUM_SPONGES] = chunk.try_into().unwrap();
        next_cycles.push(cycle);
    }

    if it.remainder().len() != 0 {
        let mut tmp = it.remainder().to_vec();
        tmp.resize(NUM_SPONGES, PendingRecord::empty());

        let cycle: [_; NUM_SPONGES] = tmp.try_into().unwrap();
        next_cycles.push(cycle);
    }

    let next_cycles: [_; MAX_PENDING_CYCLES] = next_cycles.try_into().unwrap();

    Ok((this_cycle, next_cycles))
}

use crate::vm::ports::ArithmeticFlagsPort;

pub fn select_flags<'a, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    current_flags: &ArithmeticFlagsPort<E>,
    application_results_it: impl std::iter::Iterator<
        Item = (Boolean, &'a OpcodePartialApplicationResult<E, PropsMarker>),
    >,
) -> Result<ArithmeticFlagsPort<E>, SynthesisError> {
    let of_data = vec![];
    let eq_data = vec![];
    let gt_data = vec![];

    let mut all = [of_data, eq_data, gt_data];

    for (_applies, application_result) in application_results_it {
        for (applies, flags) in application_result.flags.iter() {
            let of = flags.overflow_or_less_than;
            let eq = flags.equal;
            let gt = flags.greater_than;

            for (dst, src) in all.iter_mut().zip([of, eq, gt].into_iter()) {
                // empty
                if dst.is_empty() {
                    // form a partition by placing a source variable (for CircuitEq purposes) and applicability
                    dst.push((src, vec![*applies]));
                } else {
                    // try to find partition id that we can use
                    let mut found = false;
                    let mut idx = 0;
                    for (i, existing_partition) in dst.iter_mut().enumerate() {
                        if CircuitEq::<E>::eq(&existing_partition.0, &src) {
                            idx = i;
                            found = true;
                            break;
                        }
                    }

                    if found {
                        dst[idx].1.push(*applies);
                    } else {
                        dst.push((src, vec![*applies]));
                    }
                }
            }
        }
    }

    // we know that 1 opcode applies, so we are safe to select

    let [mut of_data, mut eq_data, mut gt_data] = all;

    // this is stable sort, we are good for circuit purposes
    of_data.sort_by(|a, b| b.1.len().cmp(&a.1.len())); // descending
    eq_data.sort_by(|a, b| b.1.len().cmp(&a.1.len())); // descending
    gt_data.sort_by(|a, b| b.1.len().cmp(&a.1.len())); // descending

    let mut of = current_flags.overflow_or_less_than;
    for (result, bools) in of_data.into_iter() {
        let should_apply = smart_or(cs, &bools)?;
        of = Boolean::conditionally_select(cs, &should_apply, &result, &of)?;
    }

    let mut eq = current_flags.equal;
    for (result, bools) in eq_data.into_iter() {
        let should_apply = smart_or(cs, &bools)?;
        eq = Boolean::conditionally_select(cs, &should_apply, &result, &eq)?;
    }

    let mut gt = current_flags.greater_than;
    for (result, bools) in gt_data.into_iter() {
        let should_apply = smart_or(cs, &bools)?;
        gt = Boolean::conditionally_select(cs, &should_apply, &result, &gt)?;
    }

    let new_flags = ArithmeticFlagsPort {
        overflow_or_less_than: of,
        equal: eq,
        greater_than: gt,
        _marker: std::marker::PhantomData,
    };

    Ok(new_flags)
}
