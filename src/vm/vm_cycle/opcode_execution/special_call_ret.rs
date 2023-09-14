use super::*;
use crate::vm::primitives::register_view::*;
use crate::vm::vm_state::GlobalContext;
use cs_derive::*;

use crate::project_ref;

use zkevm_opcode_defs::{
    FarCallForwardPageType, RetForwardPageType, FAR_CALL_CONSTRUCTOR_CALL_BYTE_IDX,
    FAR_CALL_SHARD_ID_BYTE_IDX, FAR_CALL_SYSTEM_CALL_BYTE_IDX, UNMAPPED_PAGE,
};

pub const SPECIALIZED_CALL_RET_MARKER: u64 = (1 << 10) + 1;

pub(crate) fn apply_specialized_call_ret<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    opcode_carry_parts: &OpcodeCarryParts<E>,
    global_context: &GlobalContext<E>,
    optimizer: &mut OptimizationContext<E>,
    round_function: &R,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<OpcodePartialApplicationResult<E, SpecializedImplementationPropsMarker>, SynthesisError>
{
    // near_call, far_call and ret have a lot in common:
    // - they do not use memory as input operands
    // - they do not write to registers in normall addressing
    // - they modify callstack (pc, ergs, etc)
    // - they modify states of forward/rollback queues

    // Largely for the last two points they are implemented all together

    // The strategy is to:
    // - determine the next callstack candidate if we call
    // - detemine next callstack candidate if we return
    // - make the sponges candidates based on the direction
    // - perform selection of the callstack current value and the stack state

    let n = cs.get_current_aux_gate_number();

    // far call and ret share some ABI, we can validate them
    let (fat_ptr, common_abi_flags, ptr_validation_data) =
        parse_common_abi_part(cs, &common_opcode_state.src0_view, optimizer)?;

    let near_call_data = callstack_candidate_for_near_call(
        cs,
        current_state,
        common_opcode_state,
        opcode_carry_parts,
        optimizer,
        witness_oracle,
    )?;

    let far_call_data = callstack_candidate_for_far_call(
        cs,
        current_state,
        common_opcode_state,
        opcode_carry_parts,
        round_function,
        optimizer,
        witness_oracle,
        global_context,
        &fat_ptr,
        &common_abi_flags,
        &ptr_validation_data,
    )?;

    let ret_data = callstack_candidate_for_ret(
        cs,
        current_state,
        common_opcode_state,
        opcode_carry_parts,
        optimizer,
        witness_oracle,
        &fat_ptr,
        &common_abi_flags,
        &ptr_validation_data,
    )?;

    // select callstack that will become current

    let NearCallData {
        applies: apply_near_call,
        old_context: old_context_for_near_call,
        new_context: new_context_for_near_call,
    } = near_call_data;

    let FarCallData {
        applies: apply_far_call,
        old_context: old_context_for_far_call,
        new_context: new_context_for_far_call,
        new_decommittment_queue_state,
        new_decommittment_queue_len,
        new_forward_queue_state: new_forward_queue_state_for_far_call,
        new_forward_queue_len: new_forward_queue_len_for_far_call,
        pending_sponges,
        updated_registers: updated_registers_for_far_call,
        new_memory_pages_counter,
        zero_out_specific_registers: zero_out_specific_registers_from_far_call,
        remove_ptr_on_specific_registers: remove_ptr_on_specific_registers_from_far_call,
        pending_exception: pending_exception_from_far_call,
    } = far_call_data;

    let RetData {
        applies: apply_ret,
        new_context: new_context_for_ret,
        originally_popped_context: originally_popped_context_for_ret,
        previous_callstack_state: previous_callstack_state_for_ret,
        new_forward_queue_state: new_forward_queue_state_for_ret,
        new_forward_queue_len: new_forward_queue_len_for_ret,
        updated_registers: updated_registers_for_ret,
        did_return_from_far_call,
        is_panic: is_ret_panic,
        update_specific_registers_on_ret,
        zero_out_specific_registers: zero_out_specific_registers_from_far_return,
        remove_ptr_on_specific_registers: remove_ptr_on_specific_registers_from_far_return,
    } = ret_data;

    let is_call_like = smart_or(cs, &[apply_near_call, apply_far_call])?;
    let globally_apply = smart_or(cs, &[is_call_like, apply_ret])?;
    let is_ret_panic_if_apply = smart_and(cs, &[is_ret_panic, apply_ret])?;
    let pending_exception = smart_and(cs, &[pending_exception_from_far_call, apply_far_call])?;

    let current_frame_is_local = current_state
        .callstack
        .current_context
        .saved_context
        .extension
        .is_local_call;
    let is_far_return = smart_and(cs, &[apply_ret, current_frame_is_local.not()])?;
    let reset_context_value = smart_or(cs, &[is_far_return, apply_far_call])?;

    let update_specific_registers_common =
        smart_or(cs, &[apply_far_call, update_specific_registers_on_ret])?;

    // we only need select between candidates, and later on we will select on higher level between current and candidate from (near_call/far_call/ret)

    let mut new_callstack_entry = ExecutionContextRecord::conditionally_select(
        cs,
        &apply_far_call,
        &new_context_for_far_call,
        &new_context_for_near_call,
    )?;

    new_callstack_entry = ExecutionContextRecord::conditionally_select(
        cs,
        &apply_ret,
        &new_context_for_ret,
        &new_callstack_entry,
    )?;

    // this one will be largely no-op
    let mut old_callstack_entry = ExecutionContextRecord::conditionally_select(
        cs,
        &apply_far_call,
        &old_context_for_far_call,
        &old_context_for_near_call,
    )?;

    old_callstack_entry = ExecutionContextRecord::conditionally_select(
        cs,
        &apply_ret,
        &originally_popped_context_for_ret,
        &old_callstack_entry,
    )?;

    // manual implementation of the stack: we either take a old entry and hash along with the saved context for call-like, or one popped in case of ret

    let initial_state_to_use_for_sponge = <[Num<E>; 3]>::conditionally_select(
        cs,
        &apply_ret,
        &previous_callstack_state_for_ret,
        &current_state.callstack.stack_sponge_state,
    )?;

    use crate::vm::vm_state::saved_contract_context::CallstackSpongeQueue;

    // if crate::VERBOSE_CIRCUITS && apply_near_call.get_value().unwrap_or(false) {
    //     use crate::traits::cs_encodable::CircuitFixedLengthEncodable;
    //     use crate::traits::cs_witnessable::CSWitnessable;
    //     let witness = old_callstack_entry.create_witness();
    //     dbg!(witness);
    //     dbg!(Num::get_value_multiple(&CircuitFixedLengthEncodable::encode(&old_callstack_entry, cs)?));
    //     dbg!(Num::get_value_multiple(&initial_state_to_use_for_sponge));
    //     println!("Pushed to the stack for local call");
    // }

    // if crate::VERBOSE_CIRCUITS && apply_far_call.get_value().unwrap_or(false) {
    //     use crate::traits::cs_encodable::CircuitFixedLengthEncodable;
    //     use crate::traits::cs_witnessable::CSWitnessable;
    //     let witness = old_callstack_entry.create_witness();
    //     dbg!(witness);
    //     dbg!(Num::get_value_multiple(&CircuitFixedLengthEncodable::encode(&old_callstack_entry, cs)?));
    //     dbg!(Num::get_value_multiple(&initial_state_to_use_for_sponge));
    //     println!("Pushed to the stack for far call");
    // }

    // if crate::VERBOSE_CIRCUITS && apply_ret.get_value().unwrap_or(false) {
    //     use crate::traits::cs_encodable::CircuitFixedLengthEncodable;
    //     use crate::traits::cs_witnessable::CSWitnessable;
    //     let witness = old_callstack_entry.create_witness();
    //     dbg!(witness);
    //     dbg!(Num::get_value_multiple(&CircuitFixedLengthEncodable::encode(&old_callstack_entry, cs)?));
    //     dbg!(Num::get_value_multiple(&initial_state_to_use_for_sponge));
    //     println!("Popped from the stack");
    // }

    let (states, _) = CallstackSpongeQueue::push_and_output_states_relation_raw(
        cs,
        &old_callstack_entry,
        &Boolean::constant(true),
        initial_state_to_use_for_sponge,
        UInt32::zero(),
        round_function,
    )?;

    assert_eq!(states.len(), 3);

    let potential_final_state = states.last().unwrap().1;

    // compare if ret
    for (a, b) in potential_final_state
        .iter()
        .zip(current_state.callstack.stack_sponge_state.iter())
    {
        Num::conditionally_enforce_equal(cs, &apply_ret, a, b)?;
    }

    let new_callstack_state = <[Num<E>; 3]>::conditionally_select(
        cs,
        &apply_ret,
        &previous_callstack_state_for_ret,
        &potential_final_state,
    )?;

    // if crate::VERBOSE_CIRCUITS && apply_near_call.get_value().unwrap_or(false) {
    //     println!("Expected sponge for NEAR CALL");
    //     dbg!(Num::get_value_multiple(&new_callstack_state));
    // }

    // if crate::VERBOSE_CIRCUITS && apply_far_call.get_value().unwrap_or(false) {
    //     println!("Expected sponge for FAR CALL");
    //     dbg!(Num::get_value_multiple(&new_callstack_state));
    // }

    // if crate::VERBOSE_CIRCUITS && apply_ret.get_value().unwrap_or(false) {
    //     println!("Expected sponge for RET");
    //     dbg!(Num::get_value_multiple(&new_callstack_state));
    // }

    let depth_increased = current_state
        .callstack
        .context_stack_depth
        .increment_unchecked(cs)?;
    let (depth_decreased, uf) = current_state
        .callstack
        .context_stack_depth
        .sub_using_delayed_bool_allocation(cs, &UInt32::from_uint(1), optimizer)?;

    can_not_be_false_if_flagged(cs, &uf.not(), &apply_ret)?;

    let new_callstack_depth =
        UInt32::conditionally_select(cs, &apply_ret, &depth_decreased, &depth_increased)?;

    // assemble a new callstack in full
    use crate::vm::vm_state::callstack::Callstack;

    let new_log_queue_forward_tail = Num::conditionally_select(
        cs,
        &apply_ret,
        &new_forward_queue_state_for_ret,
        &new_forward_queue_state_for_far_call,
    )?;

    let new_log_queue_forward_len = UInt32::conditionally_select(
        cs,
        &apply_ret,
        &new_forward_queue_len_for_ret,
        &new_forward_queue_len_for_far_call,
    )?;

    let new_context = FullExecutionContext {
        saved_context: new_callstack_entry,
        log_queue_forward_tail: new_log_queue_forward_tail,
        log_queue_forward_part_length: new_log_queue_forward_len,
    };

    let new_callstack = Callstack {
        current_context: new_context,
        context_stack_depth: new_callstack_depth,
        stack_sponge_state: new_callstack_state,
    };

    let marker = SpecializedImplementationPropsMarker::CallRet(
        zkevm_opcode_defs::NearCallOpcode,
        zkevm_opcode_defs::FarCallOpcode::Normal,
        zkevm_opcode_defs::RetOpcode::Ok,
    );

    let t = smart_and(cs, &[apply_ret, did_return_from_far_call])?;
    let new_did_call_or_ret_recently = smart_or(cs, &[t, apply_far_call])?;

    let mut all_sponge_requests = vec![];
    for (initial_state, final_state) in states.into_iter() {
        let record = PendingRecord {
            initial_state,
            final_state,
            is_used: globally_apply,
        };
        all_sponge_requests.push(record);
    }

    all_sponge_requests.extend(pending_sponges);

    assert_eq!(all_sponge_requests.len(), 7);

    let mut specific_registers_updates = Vec::with_capacity(2);

    assert_eq!(updated_registers_for_ret.len(), 1);
    assert_eq!(updated_registers_for_far_call.len(), 2);

    // here we do some manual work

    {
        let reg_1_from_far_call = updated_registers_for_far_call[0].clone();
        let reg_1_from_ret = updated_registers_for_ret[0].clone();

        assert_eq!(reg_1_from_far_call.0, reg_1_from_ret.0);
        assert_eq!(reg_1_from_far_call.0, 0);

        let c = Register::conditionally_select(
            cs,
            &update_specific_registers_on_ret,
            &reg_1_from_ret.1,
            &reg_1_from_far_call.1,
        )?;

        specific_registers_updates.push((
            reg_1_from_far_call.0,
            update_specific_registers_common,
            c,
        ));
    }
    {
        // only far call updates reg2, so we select manually
        let reg_2_from_far_call = updated_registers_for_far_call[1].clone();
        assert_eq!(zero_out_specific_registers_from_far_return[0].1, 1);
        assert_eq!(reg_2_from_far_call.0, 1);

        // no PTR marker, zero value
        let empty_register = Register::empty();

        let c = Register::conditionally_select(
            cs,
            &apply_far_call,
            &reg_2_from_far_call.1,
            &empty_register,
        )?;

        specific_registers_updates.push((
            reg_2_from_far_call.0,
            update_specific_registers_common,
            c,
        ));
    }

    // now we should have only common subset of zeroing-out and removing ptr markers

    let mut zero_out_specific_registers = Vec::with_capacity(16);

    assert_eq!(
        zero_out_specific_registers_from_far_call.len() + 1,
        zero_out_specific_registers_from_far_return.len()
    );

    for (a, b) in zero_out_specific_registers_from_far_call.into_iter().zip(
        zero_out_specific_registers_from_far_return
            .into_iter()
            .skip(1),
    ) {
        assert_eq!(a.1, b.1);

        let final_marker = Boolean::conditionally_select(cs, &apply_far_call, &a.0, &b.0)?;
        let final_marker = Boolean::conditionally_select(
            cs,
            &apply_near_call,
            &Boolean::constant(false),
            &final_marker,
        )?;

        zero_out_specific_registers.push((final_marker, a.1));
    }

    let mut remove_ptr_on_specific_registers = Vec::with_capacity(16);

    assert_eq!(
        remove_ptr_on_specific_registers_from_far_call.len() + 1,
        remove_ptr_on_specific_registers_from_far_return.len()
    );

    for (a, b) in remove_ptr_on_specific_registers_from_far_call
        .into_iter()
        .zip(
            remove_ptr_on_specific_registers_from_far_return
                .into_iter()
                .skip(1),
        )
    {
        assert_eq!(a.1, b.1);

        let final_marker = Boolean::conditionally_select(cs, &apply_far_call, &a.0, &b.0)?;
        let final_marker = Boolean::conditionally_select(
            cs,
            &apply_near_call,
            &Boolean::constant(false),
            &final_marker,
        )?;

        remove_ptr_on_specific_registers.push((final_marker, a.1));
    }

    // all the opcodes reset
    let mut new_flags = common_opcode_state.reseted_flags;
    new_flags.overflow_or_less_than = is_ret_panic_if_apply;

    witness_oracle.report_new_callstack_frame(
        &new_callstack.current_context.saved_context,
        new_callstack_depth,
        &is_call_like,
        &globally_apply,
    );

    let result = OpcodePartialApplicationResult {
        marker,
        applies: globally_apply,
        pending_sponges: all_sponge_requests,
        dst0_value: None,
        dst1_value: None,
        flags: vec![(globally_apply, new_flags)], // we it does intersect, but only very partially, so we are ok
        specific_registers_updates: specific_registers_updates,
        zero_out_specific_registers,
        remove_ptr_on_specific_registers,
        callstack: Some(new_callstack),
        ergs_left: None, // we do update the full callstack!
        new_pc: None,
        new_ergs_per_pubdata_byte: None,
        new_tx_number_in_block: None,
        new_memory_pages_counter: Some(new_memory_pages_counter),
        new_did_call_or_ret_recently: Some(new_did_call_or_ret_recently),
        pending_exception: Some(pending_exception),
        new_forward_queue_state: None, // we do update the full callstack!
        new_forward_queue_length: None, // we do update the full callstack!
        new_rollback_queue_state: None,
        new_rollback_queue_length: None,
        update_decommittment_queue: Some(apply_far_call),
        new_decommittment_queue_state: Some(new_decommittment_queue_state),
        new_decommittment_queue_length: Some(new_decommittment_queue_len),
        new_memory_queue_state: None,
        new_memory_queue_length: None,
        pending_arithmetic_operations: None,
        context_u128_new_value: Some((reset_context_value, [UInt64::zero(); 2])),
        new_heap_upper_bound: None,
        new_aux_heap_upper_bound: None,
    };

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for merged near/far call and ret", gates_used);
    // dbg!(_message);

    Ok(result)
}

use crate::vm::vm_state::execution_context::FullExecutionContext;
use crate::vm::vm_state::saved_contract_context::ExecutionContextRecord;
use crate::vm::vm_state::PendingRecord;

struct NearCallData<E: Engine> {
    applies: Boolean,
    old_context: ExecutionContextRecord<E>,
    new_context: ExecutionContextRecord<E>,
    // we do not need to change queues on call
}

pub struct NearCallABI<E: Engine> {
    pub ergs_passed: UInt32<E>,
}

impl<E: Engine> NearCallABI<E> {
    pub fn from_register_view(input: &RegisterInputView<E>) -> Self {
        Self {
            ergs_passed: input.u32x8_view.unwrap()[0],
        }
    }
}

use crate::traits::*;
use cs_derive::*;

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct FatPtrInABI<E: Engine> {
    pub offset: UInt32<E>,
    pub page: UInt32<E>,
    pub start: UInt32<E>,
    pub length: UInt32<E>,
}

impl<E: Engine> FatPtrInABI<E> {
    pub(crate) fn parse_and_validate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        input: &RegisterInputView<E>,
        as_fresh: Boolean,
        optimizer: &mut OptimizationContext<E>,
    ) -> Result<(Self, UInt32<E>, Boolean, Boolean), SynthesisError> {
        // we can never address a range [2^32 - 32..2^32] this way, but we don't care because
        // it's impossible to pay for such memory growth
        let offset = input.u32x8_view.unwrap()[0];
        let page = input.u32x8_view.unwrap()[1];
        let start = input.u32x8_view.unwrap()[2];
        let length = input.u32x8_view.unwrap()[3];

        let offset_is_zero = offset.is_zero(cs)?;
        let mut invalid = smart_and(cs, &[offset_is_zero.not(), as_fresh])?;

        let (end_non_inclusive, out_of_bounds) =
            start.add_using_delayed_bool_allocation(cs, &length, optimizer)?;

        // check that we do not have overflows in addressable range
        let is_in_bounds = out_of_bounds.not();

        // offset <= length
        let (_, uf) = length.sub_using_delayed_bool_allocation(cs, &offset, optimizer)?;
        let is_addresable = uf.not();

        invalid = smart_or(
            cs,
            &[
                invalid,
                out_of_bounds,
                is_in_bounds.not(),
                is_addresable.not(),
            ],
        )?;

        let offset = offset.mask(cs, &invalid.not())?;
        let page = page.mask(cs, &invalid.not())?;
        let start = start.mask(cs, &invalid.not())?;
        let length = length.mask(cs, &invalid.not())?;

        let new = Self {
            offset,
            page,
            start,
            length,
        };

        Ok((new, end_non_inclusive, invalid, out_of_bounds))
    }

    pub(crate) fn mask_into_empty<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        set_empty: Boolean,
    ) -> Result<Self, SynthesisError> {
        let offset = self.offset.mask(cs, &set_empty.not())?;
        let page = self.page.mask(cs, &set_empty.not())?;
        let start = self.start.mask(cs, &set_empty.not())?;
        let length = self.length.mask(cs, &set_empty.not())?;

        let new = Self {
            offset,
            page,
            start,
            length,
        };
        Ok(new)
    }

    // ONLY call after validations
    pub(crate) fn readjust<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        optimizer: &mut OptimizationContext<E>,
    ) -> Result<Self, SynthesisError> {
        // if we have prevalidated everything, then we KNOW that "length + start" doesn't overflow and is within addressable bound,
        // and that offset < length, so overflows here can be ignored
        let (new_start, _of) =
            self.start
                .add_using_delayed_bool_allocation(cs, &self.offset, optimizer)?;
        let (new_length, _uf) =
            self.length
                .sub_using_delayed_bool_allocation(cs, &self.offset, optimizer)?;

        let new = Self {
            offset: UInt32::zero(),
            page: self.page,
            start: new_start,
            length: new_length,
        };

        Ok(new)
    }

    pub(crate) fn into_register<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<Register<E>, SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.offset.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.page.inner, shifts[32]);
        lc.add_assign_number_with_coeff(&self.start.inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.length.inner, shifts[96]);
        let low = UInt128::from_num_unchecked(lc.into_num(cs)?);

        let result = Register {
            inner: [low, UInt128::zero()],
            is_ptr: Boolean::constant(true),
        };

        Ok(result)
    }
}

#[derive(CSAllocatable, CSWitnessable)]
pub struct FarCallPartialABI<E: Engine> {
    pub ergs_passed: UInt32<E>,
    pub shard_id: UInt8<E>,
    pub constructor_call: Boolean,
    pub system_call: Boolean,
}

impl<E: Engine> FarCallPartialABI<E> {
    pub fn from_register_view<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        input: &RegisterInputView<E>,
    ) -> Result<Self, SynthesisError> {
        // low part of highest 64 bits
        let ergs_passed = input.u32x8_view.unwrap()[6];

        // higher parts of highest 64 bits, without forwarding mode
        let shard_id = input.u8x32_view.unwrap()[FAR_CALL_SHARD_ID_BYTE_IDX];
        let constructor_call = input.u8x32_view.unwrap()[FAR_CALL_CONSTRUCTOR_CALL_BYTE_IDX]
            .is_zero(cs)?
            .not();
        let system_call = input.u8x32_view.unwrap()[FAR_CALL_SYSTEM_CALL_BYTE_IDX]
            .is_zero(cs)?
            .not();

        let new = Self {
            ergs_passed,
            shard_id,
            constructor_call,
            system_call,
        };

        Ok(new)
    }
}

fn callstack_candidate_for_near_call<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    opcode_carry_parts: &OpcodeCarryParts<E>,
    optimizer: &mut OptimizationContext<E>,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<NearCallData<E>, SynthesisError> {
    // new callstack should be just the same a the old one, but we also need to update the pricing for pubdata in the rare case
    let opcode = zkevm_opcode_defs::Opcode::NearCall(zkevm_opcode_defs::NearCallOpcode);

    let execute = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        println!("Executing LOCAL CALL");
    }
    let mut current_callstack_entry = current_state
        .callstack
        .current_context
        .saved_context
        .clone();
    // perform all known modifications, like PC/SP saving
    current_callstack_entry.common_part.pc = opcode_carry_parts.pc_plus_one;

    // for NEAR CALL the next callstack entry is largely the same
    let mut new_callstack_entry = current_callstack_entry.clone();
    // on call-like path we continue the forward queue, but have to allocate the rollback queue state from witness
    let call_timestamp = current_state.timestamp;
    let potential_rollback_queue_segment_tail =
        witness_oracle.get_rollback_queue_tail_witness_for_call(call_timestamp, &execute);

    let potential_rollback_queue_segment_tail =
        Num::alloc(cs, potential_rollback_queue_segment_tail)?;
    new_callstack_entry.common_part.reverted_queue_tail = potential_rollback_queue_segment_tail;
    new_callstack_entry.common_part.reverted_queue_head = potential_rollback_queue_segment_tail;
    new_callstack_entry.common_part.reverted_queue_segment_len = UInt32::<E>::zero();

    let dst_pc = common_opcode_state.decoded_opcode.imm0;
    let eh_pc = common_opcode_state.decoded_opcode.imm1;

    let near_call_abi = NearCallABI::from_register_view(&common_opcode_state.src0_view);
    let pass_all_ergs = near_call_abi.ergs_passed.is_zero(cs)?;

    let preliminary_ergs_left = common_opcode_state.preliminary_ergs_left;

    // we did spend some ergs on decoding, so we use one from prestate
    let ergs_to_pass = UInt32::conditionally_select(
        cs,
        &pass_all_ergs,
        &preliminary_ergs_left,
        &near_call_abi.ergs_passed,
    )?;

    let (remaining_for_this_context, uf) =
        preliminary_ergs_left.sub_using_delayed_bool_allocation(cs, &ergs_to_pass, optimizer)?;

    let remaining_ergs_if_pass = remaining_for_this_context;
    let passed_ergs_if_pass = ergs_to_pass;

    // if underflow than we pass everything!
    let remaining_ergs_if_pass =
        UInt32::conditionally_select(cs, &uf, &UInt32::zero(), &remaining_ergs_if_pass)?;

    let passed_ergs_if_pass =
        UInt32::conditionally_select(cs, &uf, &preliminary_ergs_left, &passed_ergs_if_pass)?;

    current_callstack_entry.common_part.ergs_remaining = remaining_ergs_if_pass;
    witness_oracle.push_callstack_witness(
        &current_callstack_entry,
        &current_state.callstack.context_stack_depth,
        &execute,
    );

    // ---------------------
    // actually "apply" far call

    new_callstack_entry.common_part.ergs_remaining = passed_ergs_if_pass;
    new_callstack_entry.common_part.pc = dst_pc;
    new_callstack_entry.common_part.exception_handler_loc = eh_pc;
    new_callstack_entry.extension.is_local_call = Boolean::constant(true);

    let full_data = NearCallData {
        applies: execute,
        old_context: current_callstack_entry,
        new_context: new_callstack_entry,
    };

    Ok(full_data)
}

struct FarCallData<E: Engine> {
    applies: Boolean,
    old_context: ExecutionContextRecord<E>,
    new_context: ExecutionContextRecord<E>,
    new_decommittment_queue_state: [Num<E>; 3],
    new_decommittment_queue_len: UInt32<E>,
    new_forward_queue_state: Num<E>,
    new_forward_queue_len: UInt32<E>,
    pending_sponges: Vec<PendingRecord<E, 3>>,
    updated_registers: Vec<(usize, Register<E>)>,
    zero_out_specific_registers: Vec<(Boolean, usize)>,
    remove_ptr_on_specific_registers: Vec<(Boolean, usize)>,
    pending_exception: Boolean,
    new_memory_pages_counter: UInt32<E>,
}

fn callstack_candidate_for_far_call<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    opcode_carry_parts: &OpcodeCarryParts<E>,
    round_function: &R,
    optimizer: &mut OptimizationContext<E>,
    witness_oracle: &mut impl WitnessOracle<E>,
    global_context: &GlobalContext<E>,
    fat_ptr: &FatPtrInABI<E>,
    common_abi_flags: &CommonABIFlags,
    pointer_validation_data: &FatPtrValidationData<E>,
) -> Result<FarCallData<E>, SynthesisError> {
    // new callstack should be just the same a the old one, but we also need to update the pricing for pubdata in the rare case

    let opcode = zkevm_opcode_defs::Opcode::FarCall(zkevm_opcode_defs::FarCallOpcode::Normal);

    let execute = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        println!("Executing FAR CALL");
    }
    let is_normal_call = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(zkevm_opcode_defs::Opcode::FarCall(
            zkevm_opcode_defs::FarCallOpcode::Normal,
        ));
    let is_delegated_call = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(zkevm_opcode_defs::Opcode::FarCall(
            zkevm_opcode_defs::FarCallOpcode::Delegate,
        ));
    let is_mimic_call = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(zkevm_opcode_defs::Opcode::FarCall(
            zkevm_opcode_defs::FarCallOpcode::Mimic,
        ));
    let is_kernel_mode = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .is_kernel_mode;
    let mut current_callstack_entry = current_state
        .callstack
        .current_context
        .saved_context
        .clone();
    // perform all known modifications, like PC/SP saving
    current_callstack_entry.common_part.pc = opcode_carry_parts.pc_plus_one;

    // we need a completely fresh one
    let mut new_callstack_entry = ExecutionContextRecord::uninitialized();
    // apply memory stipends right away
    new_callstack_entry.common_part.heap_upper_bound =
        UInt32::from_uint(zkevm_opcode_defs::system_params::NEW_FRAME_MEMORY_STIPEND);
    new_callstack_entry.common_part.aux_heap_upper_bound =
        UInt32::from_uint(zkevm_opcode_defs::system_params::NEW_FRAME_MEMORY_STIPEND);

    // now also create target for mimic
    let implicit_mimic_call_reg = current_state.registers
        [zkevm_opcode_defs::definitions::far_call::CALL_IMPLICIT_PARAMETER_REG_IDX as usize]
        .clone();
    // here we have to pay the cost of full decomposition
    let highest = implicit_mimic_call_reg.inner[1].decompose_into_uint16_in_place(cs)?;

    // - get code destination address
    // - resolve caller/callee dependencies
    // - resolve calldata page
    // - resolve ergs

    let shifts = compute_shifts::<E::Fr>();
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&implicit_mimic_call_reg.inner[0].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&highest[0].inner, shifts[128]);
    lc.add_assign_number_with_coeff(&highest[1].inner, shifts[144]);
    let caller_address_for_mimic = UInt160::from_num_unchecked(lc.into_num(cs)?);

    // in src1 lives the destination
    // in src0 lives the ABI

    let mut far_call_abi =
        FarCallPartialABI::from_register_view(cs, &common_opcode_state.src0_view)?;

    // src1 is target address
    let destination_address = common_opcode_state.src1_view.lowest160.unwrap();
    let destination_decomposition = common_opcode_state.src1_view.decomposed_lowest160.unwrap();

    use zkevm_opcode_defs::{FAR_CALL_SHARD_FLAG_IDX, FAR_CALL_STATIC_FLAG_IDX};
    let is_static_call = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[FAR_CALL_STATIC_FLAG_IDX];
    let is_call_shard = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[FAR_CALL_SHARD_FLAG_IDX];

    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        if is_normal_call.get_value().unwrap_or(false) {
            println!("Normal call");
        }
        if is_delegated_call.get_value().unwrap_or(false) {
            println!("Delegate call");
        }
        if is_mimic_call.get_value().unwrap_or(false) {
            println!("Mimic call");
        }
        if is_static_call.get_value().unwrap_or(false) {
            println!("Static call modifier");
        }
        if is_call_shard.get_value().unwrap_or(false) {
            println!("Call shard modifier call");
        }
    }

    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        if common_abi_flags
            .forward_fat_pointer
            .get_value()
            .unwrap_or(false)
        {
            println!(
                "Forwarding fat pointer {:?} on return",
                fat_ptr.create_witness().unwrap()
            );
        }
    }

    let destination_shard = far_call_abi.shard_id;
    let caller_shard_id = current_callstack_entry.common_part.this_shard_id;
    let destination_shard =
        UInt8::conditionally_select(cs, &is_call_shard, &destination_shard, &caller_shard_id)?;
    let target_is_zkporter = destination_shard.is_zero(cs)?.not();

    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        println!("Calling shard {}", destination_shard.get_value().unwrap());
        println!(
            "Calling address {}",
            destination_address.get_value().unwrap()
        );
    }

    let target_is_kernel = {
        let mut lc = LinearCombination::zero();
        // two bytes
        lc.add_assign_number_with_coeff(
            &common_opcode_state.src1_view.u8x32_view.unwrap()[2].inner,
            shifts[16],
        );
        lc.add_assign_number_with_coeff(
            &common_opcode_state.src1_view.u8x32_view.unwrap()[3].inner,
            shifts[24],
        );
        // and 32 bit word
        lc.add_assign_number_with_coeff(
            &common_opcode_state.src1_view.u32x8_view.unwrap()[3].inner,
            shifts[32],
        );
        let lowest_16_to_64 = UInt64::from_num_unchecked(lc.into_num(cs)?);

        let t0 = lowest_16_to_64.is_zero(cs)?;
        let t1 = destination_decomposition.1.is_zero(cs)?;
        let t2 = destination_decomposition.2.is_zero(cs)?;

        let target_is_kernel = smart_and(cs, &[t0, t1, t2])?;

        target_is_kernel
    };

    // mask flags in ABI if not applicable
    far_call_abi.constructor_call =
        smart_and(cs, &[far_call_abi.constructor_call, is_kernel_mode])?;
    far_call_abi.system_call = smart_and(cs, &[far_call_abi.system_call, target_is_kernel])?;

    // the same as we use for LOG
    let timestamp_to_use_for_decommittment_request =
        opcode_carry_parts.timestamp_for_first_decommit_or_precompile_read;
    let default_target_memory_page = current_state.memory_page_counter;

    // increment next counter

    use zkevm_opcode_defs::NEW_MEMORY_PAGES_PER_FAR_CALL;
    let new_base_page = current_state.memory_page_counter;
    let (new_memory_pages_counter, _) = current_state
        .memory_page_counter
        .add_using_delayed_bool_allocation(
            cs,
            &UInt32::from_uint(NEW_MEMORY_PAGES_PER_FAR_CALL),
            optimizer,
        )?;

    let new_memory_pages_counter = UInt32::conditionally_select(
        cs,
        &execute,
        &new_memory_pages_counter,
        &current_state.memory_page_counter,
    )?;

    // now we have everything to perform code read and decommittment

    let mut all_pending_sponges = vec![];

    let (
        bytecode_hash_is_trivial,
        bytecode_hash,
        (new_forward_queue_state, new_forward_queue_len),
        pending_sponges,
    ) = may_be_read_code_hash(
        cs,
        destination_decomposition,
        destination_shard,
        target_is_zkporter,
        global_context.zkporter_is_available,
        execute,
        global_context.default_aa_code_hash,
        target_is_kernel,
        current_state
            .callstack
            .current_context
            .log_queue_forward_tail,
        current_state
            .callstack
            .current_context
            .log_queue_forward_part_length,
        timestamp_to_use_for_decommittment_request,
        current_state.tx_number_in_block,
        round_function,
        optimizer,
        witness_oracle,
    )?;

    all_pending_sponges.extend(pending_sponges);

    // now we should do validation BEFORE decommittment

    let target_code_memory_page = UInt32::conditionally_select(
        cs,
        &bytecode_hash_is_trivial,
        &UInt32::<E>::zero(),
        &default_target_memory_page,
    )?;

    // first we validate if code hash is indeed in the format that we expect

    // If we do not do "constructor call" then 2nd byte should be 0,
    // otherwise it's 1

    let bytecode_hash_upper_decomposition =
        bytecode_hash.inner[3].decompose_into_uint8_in_place(cs)?;
    use zkevm_opcode_defs::versioned_hash::VersionedHashDef;

    let version_byte = bytecode_hash_upper_decomposition[7];
    let versioned_byte_is_valid = UInt8::equals(
        cs,
        &version_byte,
        &UInt8::from_uint(zkevm_opcode_defs::ContractCodeSha256::VERSION_BYTE),
    )?;

    let marker_byte = bytecode_hash_upper_decomposition[6];
    let is_normal_call_marker = marker_byte.is_zero(cs)?;
    let is_constructor_call_marker = UInt8::equals(
        cs,
        &marker_byte,
        &UInt8::from_uint(zkevm_opcode_defs::ContractCodeSha256::YET_CONSTRUCTED_MARKER),
    )?;
    let unknown_marker = smart_and(
        cs,
        &[
            is_normal_call_marker.not(),
            is_constructor_call_marker.not(),
        ],
    )?;

    // NOTE: if bytecode hash is trivial then it's 0, so version byte is not valid!
    let code_format_exception = smart_or(cs, &[versioned_byte_is_valid.not(), unknown_marker])?;

    // we do not remask right away yet

    let can_call_normally = smart_and(
        cs,
        &[is_normal_call_marker, far_call_abi.constructor_call.not()],
    )?;
    let can_call_constructor = smart_and(
        cs,
        &[is_constructor_call_marker, far_call_abi.constructor_call],
    )?;
    let can_call_code = smart_or(cs, &[can_call_normally, can_call_constructor])?;

    // we also tentatively recompose bytecode hash in it's "storage" format

    // we always mask marker byte for our decommittment requests
    let marker_byte_masked = UInt8::zero();

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&bytecode_hash_upper_decomposition[0].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&bytecode_hash_upper_decomposition[1].inner, shifts[8]);
    lc.add_assign_number_with_coeff(&bytecode_hash_upper_decomposition[2].inner, shifts[16]);
    lc.add_assign_number_with_coeff(&bytecode_hash_upper_decomposition[3].inner, shifts[24]);
    lc.add_assign_number_with_coeff(&bytecode_hash_upper_decomposition[4].inner, shifts[32]);
    lc.add_assign_number_with_coeff(&bytecode_hash_upper_decomposition[5].inner, shifts[40]);
    lc.add_assign_number_with_coeff(&marker_byte_masked.inner, shifts[48]);
    lc.add_assign_number_with_coeff(&version_byte.inner, shifts[56]);
    let bytecode_at_rest_top_word = UInt64::from_num_unchecked(lc.into_num(cs)?);

    let bytecode_at_storage_format = UInt256 {
        inner: [
            bytecode_hash.inner[0],
            bytecode_hash.inner[1],
            bytecode_hash.inner[2],
            bytecode_at_rest_top_word,
        ],
    };

    let masked_value_if_mask = UInt256::conditionally_select(
        cs,
        &target_is_kernel,
        &UInt256::zero(),
        &global_context.default_aa_code_hash,
    )?;

    let masked_bytecode_hash = UInt256::conditionally_select(
        cs,
        &can_call_code,
        &bytecode_at_storage_format,
        &masked_value_if_mask,
    )?;

    // we also need masked bytecode length
    let masked_bytecode_hash_upper_decomposition =
        masked_bytecode_hash.inner[3].decompose_into_uint8_in_place(cs)?;
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(
        &masked_bytecode_hash_upper_decomposition[4].inner,
        shifts[0],
    );
    lc.add_assign_number_with_coeff(
        &masked_bytecode_hash_upper_decomposition[5].inner,
        shifts[8],
    );
    let mut code_hash_length_in_words = UInt16::from_num_unchecked(lc.into_num(cs)?);

    // if we call now-in-construction system contract, then we formally mask into 0 (even though it's not needed),
    // and we should put an exception here

    let call_now_in_construction_kernel = smart_and(cs, &[can_call_code.not(), target_is_kernel])?;

    drop(bytecode_hash);

    // at the end of the day all our exceptions will lead to memory page being 0

    code_hash_length_in_words = code_hash_length_in_words.mask(cs, &code_format_exception.not())?;

    // exceptions, along with `bytecode_hash_is_trivial` indicate whether we will or will decommit code
    // into memory, or will just use UNMAPPED_PAGE

    // NOTE: if bytecode hash is trivial, then our bytecode will not pass those checks
    let mut exceptions = Vec::with_capacity(8);
    exceptions.push(code_format_exception);
    exceptions.push(call_now_in_construction_kernel);

    // resolve passed ergs, passed calldata page, etc

    let fat_ptr_expected_exception = smart_and(
        cs,
        &[
            common_abi_flags.forward_fat_pointer,
            common_opcode_state.src0_view.is_ptr.not(),
        ],
    )?;
    exceptions.push(fat_ptr_expected_exception);

    let fat_ptr = fat_ptr.clone();

    exceptions.push(pointer_validation_data.invalid);

    let exceptions_collapsed = smart_or(cs, &exceptions)?;

    let fat_ptr = fat_ptr.mask_into_empty(cs, exceptions_collapsed)?;
    // also mask upped bound since we do not recompute
    let upper_bound = pointer_validation_data.upper_bound;
    // first mask to 0 if exceptions happened
    let upper_bound = upper_bound.mask(cs, &exceptions_collapsed.not())?;
    // then compute to penalize for out of memory access attemp
    let penalize_for_out_of_bounds = pointer_validation_data.memory_is_not_addressable;
    let upper_bound = UInt32::conditionally_select(
        cs,
        &penalize_for_out_of_bounds,
        &UInt32::from_uint(u32::MAX),
        &upper_bound,
    )?;

    // now we can modify fat ptr that was prevalidated
    let fat_ptr_adjusted_if_forward = fat_ptr.readjust(cs, optimizer)?;

    let page = UInt32::conditionally_select(
        cs,
        &common_abi_flags.use_heap,
        &opcode_carry_parts.heap_page,
        &opcode_carry_parts.aux_heap_page,
    )?;
    let fat_ptr_for_heaps = FatPtrInABI {
        offset: UInt32::zero(),
        page,
        start: fat_ptr.start,
        length: fat_ptr.length,
    };

    let final_fat_ptr = FatPtrInABI::conditionally_select(
        cs,
        &common_abi_flags.forward_fat_pointer,
        &fat_ptr_adjusted_if_forward,
        &fat_ptr_for_heaps,
    )?;

    // potentially pay for memory growth

    let heap_max_accessed = upper_bound.mask(cs, &common_abi_flags.use_heap)?;
    let heap_bound = current_callstack_entry.common_part.heap_upper_bound;
    let (mut heap_growth, uf) =
        heap_max_accessed.sub_using_delayed_bool_allocation(cs, &heap_bound, optimizer)?;
    heap_growth = heap_growth.mask(cs, &uf.not())?; // of we access in bounds then it's 0
    let new_heap_upper_bound =
        UInt32::conditionally_select(cs, &uf, &heap_bound, &heap_max_accessed)?;
    let grow_heap = smart_and(cs, &[common_abi_flags.use_heap, execute])?;

    let aux_heap_max_accessed = upper_bound.mask(cs, &common_abi_flags.use_aux_heap)?;
    let aux_heap_bound = current_callstack_entry.common_part.aux_heap_upper_bound;
    let (mut aux_heap_growth, uf) =
        aux_heap_max_accessed.sub_using_delayed_bool_allocation(cs, &aux_heap_bound, optimizer)?;
    aux_heap_growth = aux_heap_growth.mask(cs, &uf.not())?; // of we access in bounds then it's 0
    let new_aux_heap_upper_bound =
        UInt32::conditionally_select(cs, &uf, &aux_heap_bound, &aux_heap_max_accessed)?;
    let grow_aux_heap = smart_and(cs, &[common_abi_flags.use_aux_heap, execute])?;

    let mut growth_cost =
        UInt32::conditionally_select(cs, &grow_heap, &heap_growth, &UInt32::zero())?;

    growth_cost = UInt32::conditionally_select(cs, &grow_aux_heap, &aux_heap_growth, &growth_cost)?;

    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        println!(
            "Far call uses {} ergs for memory growth",
            growth_cost.get_value().unwrap()
        );
    }

    let (ergs_left_after_growth, uf) = opcode_carry_parts
        .preliminary_ergs_left
        .sub_using_delayed_bool_allocation(cs, &growth_cost, optimizer)?;

    let mut exceptions = vec![];
    exceptions.push(exceptions_collapsed);

    let ergs_left_after_growth = ergs_left_after_growth.mask(cs, &uf.not())?; // if not enough - set to 0
    exceptions.push(uf);

    current_callstack_entry.common_part.heap_upper_bound = UInt32::conditionally_select(
        cs,
        &grow_heap,
        &new_heap_upper_bound,
        &current_callstack_entry.common_part.heap_upper_bound,
    )?;

    current_callstack_entry.common_part.aux_heap_upper_bound = UInt32::conditionally_select(
        cs,
        &grow_aux_heap,
        &new_aux_heap_upper_bound,
        &current_callstack_entry.common_part.aux_heap_upper_bound,
    )?;

    // now any extra cost
    let callee_stipend =
        if zk_evm::opcodes::execution::far_call::FORCED_ERGS_FOR_MSG_VALUE_SIMULATOR == false {
            UInt32::zero()
        } else {
            use crate::vm::primitives::u160;
            let target_is_msg_value = UInt160::equals(
                cs,
                &destination_address,
                &UInt160::from_uint(u160::from_u64(zkevm_opcode_defs::ADDRESS_MSG_VALUE as u64)),
            )?;
            let is_system_abi = far_call_abi.system_call;
            let require_extra = smart_and(cs, &[target_is_msg_value, is_system_abi])?;

            let additive_cost = UInt32::from_uint(
                zkevm_opcode_defs::system_params::MSG_VALUE_SIMULATOR_ADDITIVE_COST,
            );
            let pubdata_cost = UInt32::from_uint(
                zkevm_opcode_defs::system_params::MSG_VALUE_SIMULATOR_PUBDATA_BYTES_TO_PREPAY,
            )
            .inner
            .mul(cs, &current_state.ergs_per_pubdata_byte.inner)?;
            let pubdata_cost = UInt32 {
                inner: pubdata_cost,
            };
            let cost = pubdata_cost.add_unchecked(cs, &additive_cost)?;

            cost.mask(cs, &require_extra)?
        };

    let (ergs_left_after_extra_costs, uf) =
        ergs_left_after_growth.sub_using_delayed_bool_allocation(cs, &callee_stipend, optimizer)?;
    let ergs_left_after_extra_costs = ergs_left_after_extra_costs.mask(cs, &uf.not())?; // if not enough - set to 0
    let callee_stipend = callee_stipend.mask(cs, &uf.not())?; // also set to 0 if we were not able to take it
    exceptions.push(uf);

    // now we can indeed decommit
    let exception = smart_or(cs, &exceptions)?;
    let should_decommit = smart_and(cs, &[execute, exception.not()])?;

    let target_code_memory_page = UInt32::conditionally_select(
        cs,
        &should_decommit,
        &target_code_memory_page,
        &UInt32::<E>::zero(),
    )?;

    let (
        not_enough_ergs_to_decommit,
        code_memory_page,
        (new_decommittment_queue_state, new_decommittment_queue_len),
        ergs_remaining_after_decommit,
        pending_sponges,
    ) = add_to_decommittment_queue(
        cs,
        should_decommit,
        ergs_left_after_extra_costs,
        masked_bytecode_hash,
        code_hash_length_in_words,
        current_state.code_decommittment_queue_state,
        current_state.code_decommittment_queue_length,
        timestamp_to_use_for_decommittment_request,
        target_code_memory_page,
        round_function,
        optimizer,
        witness_oracle,
    )?;

    let exception = smart_or(cs, &[exception, not_enough_ergs_to_decommit])?;

    all_pending_sponges.extend(pending_sponges);

    // on call-like path we continue the forward queue, but have to allocate the rollback queue state from witness
    let call_timestamp = current_state.timestamp;
    let potential_rollback_queue_segment_tail =
        witness_oracle.get_rollback_queue_tail_witness_for_call(call_timestamp, &execute);

    let potential_rollback_queue_segment_tail =
        Num::alloc(cs, potential_rollback_queue_segment_tail)?;
    new_callstack_entry.common_part.reverted_queue_tail = potential_rollback_queue_segment_tail;
    new_callstack_entry.common_part.reverted_queue_head = potential_rollback_queue_segment_tail;
    new_callstack_entry.common_part.reverted_queue_segment_len = UInt32::<E>::zero();

    let dst_pc = UInt16::zero();
    let eh_pc = common_opcode_state.decoded_opcode.imm0;

    // now we should resolve all passed ergs. That means
    // that we have to read it from ABI, and then use 63/64 rule
    let preliminary_ergs_left = ergs_remaining_after_decommit;

    use crate::precompiles::keccak256::u32_div_by_constant;

    let (ergs_div_by_64, _) = u32_div_by_constant(cs, preliminary_ergs_left, 64)?;

    let max_passable =
        UInt32::from_num_unchecked(ergs_div_by_64.inner.mul(cs, &UInt32::from_uint(63).inner)?);
    let leftover =
        UInt32::from_num_unchecked(preliminary_ergs_left.inner.sub(cs, &max_passable.inner)?);
    let ergs_to_pass = far_call_abi.ergs_passed;

    let (remaining_from_max_passable, uf) =
        max_passable.sub_using_delayed_bool_allocation(cs, &ergs_to_pass, optimizer)?;
    let (leftover_and_remaining_if_no_uf, _) =
        leftover.add_using_delayed_bool_allocation(cs, &remaining_from_max_passable, optimizer)?;

    let ergs_to_pass = UInt32::conditionally_select(cs, &uf, &max_passable, &ergs_to_pass)?;

    let remaining_for_this_context =
        UInt32::conditionally_select(cs, &uf, &leftover, &leftover_and_remaining_if_no_uf)?;

    let remaining_ergs_if_pass = remaining_for_this_context;
    let passed_ergs_if_pass = ergs_to_pass;
    let passed_ergs_if_pass = callee_stipend.inner.add(cs, &passed_ergs_if_pass.inner)?;
    let passed_ergs_if_pass = UInt32 {
        inner: passed_ergs_if_pass,
    };

    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        println!(
            "Far call will pass {} ergs, with {} being max to pass",
            ergs_to_pass.get_value().unwrap(),
            max_passable.get_value().unwrap()
        );
    }

    current_callstack_entry.common_part.ergs_remaining = remaining_ergs_if_pass;

    // resolve this/callee shard
    let new_this_shard_id =
        UInt8::conditionally_select(cs, &is_delegated_call, &caller_shard_id, &destination_shard)?;

    // default is normal call
    let mut this_for_next = destination_address;
    let mut caller_for_next = current_callstack_entry.common_part.this;

    // change if delegate or mimic
    // - "this" only changed if delegate
    this_for_next = UInt160::conditionally_select(
        cs,
        &is_delegated_call,
        &current_callstack_entry.common_part.this,
        &this_for_next,
    )?;
    // "caller" changes in both cases

    caller_for_next = UInt160::conditionally_select(
        cs,
        &is_delegated_call,
        &current_callstack_entry.common_part.caller,
        &caller_for_next,
    )?;

    caller_for_next = UInt160::conditionally_select(
        cs,
        &is_mimic_call,
        &caller_address_for_mimic,
        &caller_for_next,
    )?;

    // resolve static, etc
    let next_is_static = smart_or(
        cs,
        &[
            is_static_call,
            current_callstack_entry.common_part.is_static_execution,
        ],
    )?;
    //

    // actually parts to the new one
    new_callstack_entry.common_part.ergs_remaining = passed_ergs_if_pass;
    new_callstack_entry.common_part.pc = dst_pc;
    new_callstack_entry.common_part.exception_handler_loc = eh_pc;
    new_callstack_entry.common_part.is_static_execution = next_is_static;

    // we need to decide whether new frame is kernel or not for degelatecall
    let new_frame_is_kernel = Boolean::conditionally_select(
        cs,
        &is_delegated_call,
        &current_callstack_entry.common_part.is_kernel_mode,
        &target_is_kernel,
    )?;
    new_callstack_entry.common_part.is_kernel_mode = new_frame_is_kernel;

    // code part
    new_callstack_entry.common_part.code_shard_id = destination_shard;
    new_callstack_entry.common_part.code_address = destination_address;
    // this part
    new_callstack_entry.common_part.this_shard_id = new_this_shard_id;
    new_callstack_entry.common_part.this = this_for_next;
    // caller part
    new_callstack_entry.common_part.caller = caller_for_next;
    new_callstack_entry.common_part.caller_shard_id = caller_shard_id;
    // code page
    new_callstack_entry.common_part.code_page = code_memory_page;
    // base page
    new_callstack_entry.common_part.base_page = new_base_page;
    // context u128
    // if we do delegatecall then we propagate current context value, otherwise
    // we capture the current one
    new_callstack_entry.common_part.context_u128_value_composite =
        <[UInt64<E>; 2]>::conditionally_select(
            cs,
            &is_delegated_call,
            &current_callstack_entry
                .common_part
                .context_u128_value_composite,
            &current_state.context_composite_u128,
        )?;
    // non-local call
    new_callstack_entry.extension.is_local_call = Boolean::constant(false);

    // do the witness job
    witness_oracle.push_callstack_witness(
        &current_callstack_entry,
        &current_state.callstack.context_stack_depth,
        &execute,
    );

    // and update registers following our ABI rules

    let new_r1 = final_fat_ptr.into_register(cs)?;

    let mut new_r2 = Register::zero();
    let mut lc = LinearCombination::zero();
    lc.add_assign_boolean_with_coeff(&far_call_abi.constructor_call, shifts[0]);
    lc.add_assign_boolean_with_coeff(&far_call_abi.system_call, shifts[1]);
    new_r2.inner[0] = UInt128::from_num_unchecked(lc.into_num(cs)?);

    let mut register_cleanups = Vec::with_capacity(16);
    for reg_idx in zkevm_opcode_defs::definitions::far_call::CALL_SYSTEM_ABI_REGISTERS {
        register_cleanups.push((far_call_abi.system_call.not(), reg_idx as usize));
    }
    for reg_idx in zkevm_opcode_defs::definitions::far_call::CALL_RESERVED_RANGE {
        register_cleanups.push((Boolean::constant(true), reg_idx as usize));
    }
    register_cleanups.push((
        Boolean::constant(true),
        zkevm_opcode_defs::definitions::far_call::CALL_IMPLICIT_PARAMETER_REG_IDX as usize,
    ));

    // erase markers everywhere anyway
    let mut erase_ptr_markers = Vec::with_capacity(16);
    for reg_idx in zkevm_opcode_defs::definitions::far_call::CALL_SYSTEM_ABI_REGISTERS {
        erase_ptr_markers.push((Boolean::constant(true), reg_idx as usize));
    }
    for reg_idx in zkevm_opcode_defs::definitions::far_call::CALL_RESERVED_RANGE {
        erase_ptr_markers.push((Boolean::constant(true), reg_idx as usize));
    }
    erase_ptr_markers.push((
        Boolean::constant(true),
        zkevm_opcode_defs::definitions::far_call::CALL_IMPLICIT_PARAMETER_REG_IDX as usize,
    ));

    assert_eq!(register_cleanups.len(), erase_ptr_markers.len());

    let updated_registers = vec![(0, new_r1), (1, new_r2)];

    // if we didn't decommit for ANY reason then we will have target memory page == UNMAPPED PAGE, that will trigger panic
    let full_data = FarCallData {
        applies: execute,
        old_context: current_callstack_entry,
        new_context: new_callstack_entry,
        new_decommittment_queue_state,
        new_decommittment_queue_len,
        new_forward_queue_state,
        new_forward_queue_len,
        new_memory_pages_counter,
        pending_sponges: all_pending_sponges,
        updated_registers: updated_registers,
        pending_exception: exception,
        zero_out_specific_registers: register_cleanups,
        remove_ptr_on_specific_registers: erase_ptr_markers,
    };

    Ok(full_data)
}

// We read code hash from the storage if we have enough ergs, and mask out
// a case if code hash is 0 into either default AA or 0 if destination is kernel
pub fn may_be_read_code_hash<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    target_decomposition: (UInt64<E>, UInt64<E>, UInt32<E>),
    shard_id: UInt8<E>,
    target_is_zkporter: Boolean,
    zkporter_is_available: Boolean,
    should_execute: Boolean,
    default_aa_code_hash: UInt256<E>,
    target_is_kernel: Boolean,
    forward_queue_state: Num<E>,
    forward_queue_length: UInt32<E>,
    timestamp_to_use_for_read_request: UInt32<E>,
    tx_number_in_block: UInt16<E>,
    round_function: &R,
    optimizer: &mut OptimizationContext<E>,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<
    (
        Boolean,
        UInt256<E>,
        (Num<E>, UInt32<E>),
        Vec<PendingRecord<E, 3>>,
    ),
    SynthesisError,
> {
    let target_is_porter_and_its_available =
        smart_and(cs, &[target_is_zkporter, zkporter_is_available])?;
    let can_read = smart_or(
        cs,
        &[target_is_zkporter.not(), target_is_porter_and_its_available],
    )?;
    let should_read = smart_and(cs, &[should_execute, can_read])?;
    let needs_porter_mask = smart_and(cs, &[target_is_zkporter, zkporter_is_available.not()])?;

    use crate::vm::primitives::u160;

    let mut target_as_u256 = UInt256::zero();
    target_as_u256.inner[0] = target_decomposition.0;
    target_as_u256.inner[1] = target_decomposition.1;
    target_as_u256.inner[2] = UInt64::from_num_unchecked(target_decomposition.2.inner);

    use crate::glue::aux_byte_markers::aux_byte_for_storage;
    use crate::scheduler::data_access_functions::StorageLogRecord;

    let mut storage_key = StorageLogRecord {
        address: UInt160::from_uint(u160::from_u64(
            zkevm_opcode_defs::system_params::DEPLOYER_SYSTEM_CONTRACT_ADDRESS_LOW as u64,
        )),
        key: target_as_u256,
        read_value: UInt256::zero(),
        written_value: UInt256::zero(),
        r_w_flag: Boolean::constant(false),
        aux_byte: aux_byte_for_storage::<E>(),
        rollback: Boolean::constant(false),
        is_service: Boolean::constant(false),
        shard_id: Byte::<E>::from_num_unconstrained(cs, shard_id.inner),
        tx_number_in_block,
        timestamp: timestamp_to_use_for_read_request,
    };

    let witness =
        witness_oracle.get_storage_read_witness(&storage_key, &should_read, &should_execute);
    let opcode = zkevm_opcode_defs::Opcode::FarCall(zkevm_opcode_defs::FarCallOpcode::Normal);
    let marker = opcode.variant_idx() as u64;
    let read_value = UInt256::allocate_in_optimization_context_with_applicability(
        cs,
        witness,
        optimizer,
        should_read,
        CtxMarker::from(marker as u8),
    )?;

    storage_key.read_value = read_value;
    storage_key.written_value = read_value; // our convension as in LOG opcode

    let code_hash_from_storage = read_value;

    let mut bytecode_hash = code_hash_from_storage;
    let bytecode_is_empty = bytecode_hash.is_zero(cs)?;
    let mask_for_default_aa = smart_and(
        cs,
        &[should_read, bytecode_is_empty, target_is_kernel.not()],
    )?;

    // mask based on some conventions
    // first - mask for default AA
    bytecode_hash = UInt256::conditionally_select(
        cs,
        &mask_for_default_aa,
        &default_aa_code_hash,
        &bytecode_hash,
    )?;

    // - if we couldn't read porter
    bytecode_hash =
        UInt256::conditionally_select(cs, &needs_porter_mask, &UInt256::zero(), &bytecode_hash)?;

    // bytecode is exactly 0 if we did NOT mask it into defualt AA
    let t0 = smart_and(cs, &[bytecode_is_empty, mask_for_default_aa.not()])?;
    // or if we never read, if it's unavailable porter, or if we never masked 0 into default AA
    let bytecode_hash_is_trivial = smart_or(cs, &[t0, needs_porter_mask, should_read.not()])?;

    // now process the sponges on whether we did read

    use crate::scheduler::queues::StorageLogQueue;
    let (intermediate_states, new_forward_queue_state, new_forward_queue_length) =
        StorageLogQueue::push_and_output_states_relation_raw(
            cs,
            &storage_key,
            &should_read,
            forward_queue_state,
            forward_queue_length,
            round_function,
        )?;

    let new_forward_queue_state = Num::conditionally_select(
        cs,
        &should_read,
        &new_forward_queue_state,
        &forward_queue_state,
    )?;

    let mut all_sponge_requests = vec![];

    assert_eq!(intermediate_states.len(), 3);
    for (initial_state, final_state) in intermediate_states.into_iter() {
        let pending_request = PendingRecord {
            initial_state,
            final_state,
            is_used: should_read,
        };
        all_sponge_requests.push(pending_request);
    }

    Ok((
        bytecode_hash_is_trivial,
        bytecode_hash,
        (new_forward_queue_state, new_forward_queue_length),
        all_sponge_requests,
    ))
}

pub fn add_to_decommittment_queue<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    should_decommit: Boolean,
    ergs_remaining: UInt32<E>,
    bytecode_hash: UInt256<E>,
    num_words_in_bytecode: UInt16<E>,
    current_decommittment_queue_state: [Num<E>; 3],
    current_decommittment_queue_len: UInt32<E>,
    timestamp_to_use_for_decommittment_request: UInt32<E>,
    target_memory_page: UInt32<E>,
    round_function: &R,
    optimizer: &mut OptimizationContext<E>,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<
    (
        Boolean,
        UInt32<E>,
        ([Num<E>; 3], UInt32<E>),
        UInt32<E>,
        Vec<PendingRecord<E, 3>>,
    ),
    SynthesisError,
> {
    // compute any associated extra costs

    let cost_of_decommittment = UInt32::from_num_unchecked(
        Num::Constant(u64_to_fe(
            zkevm_opcode_defs::ERGS_PER_CODE_WORD_DECOMMITTMENT as u64,
        ))
        .mul(cs, &num_words_in_bytecode.inner)?,
    );

    if crate::VERBOSE_CIRCUITS && should_decommit.get_value().unwrap_or(false) {
        println!(
            "Decommitment costs {} ergs",
            cost_of_decommittment.get_value().unwrap()
        );
    }

    let (ergs_after_decommit_may_be, uf) =
        ergs_remaining.sub_using_delayed_bool_allocation(cs, &cost_of_decommittment, optimizer)?;

    let not_enough_ergs_to_decommit = uf;
    let should_decommit = smart_and(cs, &[should_decommit, not_enough_ergs_to_decommit.not()])?;

    // if we do not decommit then we will eventually map into 0 page for 0 extra ergs
    let ergs_remaining_after_decommit = UInt32::conditionally_select(
        cs,
        &should_decommit,
        &ergs_after_decommit_may_be,
        &ergs_remaining,
    )?;

    // decommit and return new code page and queue states

    use crate::scheduler::queues::DecommitHash;
    use crate::scheduler::queues::DecommitQuery;
    let mut decommittment_request = DecommitQuery {
        root_hash: DecommitHash::AsU256(bytecode_hash),
        page: target_memory_page,
        is_first: Boolean::constant(true),
        timestamp: timestamp_to_use_for_decommittment_request,
    };

    let decommittment_witness =
        witness_oracle.get_decommittment_request_witness(&decommittment_request, &should_decommit);

    let is_first = project_ref!(decommittment_witness, is_first).copied();
    let is_first = optimizer.allocate_boolean(cs, is_first)?;

    let result_page = project_ref!(decommittment_witness, page).copied();
    let result_page = UInt32::allocate(cs, result_page)?;

    decommittment_request.is_first = is_first;
    decommittment_request.page = UInt32::conditionally_select(
        cs,
        &decommittment_request.is_first,
        &decommittment_request.page,
        &result_page,
    )?;

    // kind of refund if we didn't decommit

    let refund = smart_and(cs, &[should_decommit, is_first.not()])?;
    if crate::VERBOSE_CIRCUITS && refund.get_value().unwrap_or(false) {
        println!("WIll refund ergs for decommit");
    }
    let ergs_remaining_after_decommit =
        UInt32::conditionally_select(cs, &refund, &ergs_remaining, &ergs_remaining_after_decommit)?;

    let mut all_sponge_requests = vec![];

    // roll the decommittment queue sponge
    use crate::scheduler::queues::DecommitQueue;
    let (intermediate_states, new_decommittment_queue_len) =
        DecommitQueue::push_and_output_states_relation_raw(
            cs,
            &decommittment_request,
            &should_decommit,
            current_decommittment_queue_state,
            current_decommittment_queue_len,
            round_function,
        )?;

    assert_eq!(intermediate_states.len(), 1);

    let (initial_state, final_state) = intermediate_states[0];
    let pending_request = PendingRecord {
        initial_state,
        final_state,
        is_used: should_decommit,
    };
    all_sponge_requests.push(pending_request);

    let new_decommittment_queue_state = <[Num<E>; 3]>::conditionally_select(
        cs,
        &should_decommit,
        &final_state,
        &current_decommittment_queue_state,
    )?;

    // we use `should_decommit` as a marker that we did actually execute both read and decommittment (whether fresh or not)

    let target_memory_page = decommittment_request.page;
    let target_memory_page = UInt32::conditionally_select(
        cs,
        &should_decommit,
        &target_memory_page,
        &UInt32::from_uint(UNMAPPED_PAGE),
    )?;

    Ok((
        not_enough_ergs_to_decommit,
        target_memory_page,
        (new_decommittment_queue_state, new_decommittment_queue_len),
        ergs_remaining_after_decommit,
        all_sponge_requests,
    ))
}

struct RetData<E: Engine> {
    applies: Boolean,
    originally_popped_context: ExecutionContextRecord<E>,
    previous_callstack_state: [Num<E>; 3],
    new_context: ExecutionContextRecord<E>,
    new_forward_queue_state: Num<E>, // after we glue
    new_forward_queue_len: UInt32<E>,
    update_specific_registers_on_ret: Boolean,
    updated_registers: Vec<(usize, Register<E>)>,
    zero_out_specific_registers: Vec<(Boolean, usize)>,
    remove_ptr_on_specific_registers: Vec<(Boolean, usize)>,
    did_return_from_far_call: Boolean,
    is_panic: Boolean,
}

struct CommonABIFlags {
    use_heap: Boolean,
    use_aux_heap: Boolean,
    forward_fat_pointer: Boolean,
}

struct FatPtrValidationData<E: Engine> {
    invalid: Boolean,
    memory_is_not_addressable: Boolean,
    upper_bound: UInt32<E>,
}

fn parse_common_abi_part<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    input: &RegisterInputView<E>,
    optimizer: &mut OptimizationContext<E>,
) -> Result<(FatPtrInABI<E>, CommonABIFlags, FatPtrValidationData<E>), SynthesisError> {
    // far call and ret share ABI in their memory part and forwarding mode part

    let forwarding_mode_byte = input.u8x32_view.unwrap()
        [zkevm_opcode_defs::definitions::abi::far_call::FAR_CALL_FORWARDING_MODE_BYTE_IDX];

    let use_aux_heap = UInt8::equals(
        cs,
        &forwarding_mode_byte,
        &UInt8::<E>::from_uint(RetForwardPageType::UseAuxHeap as u8),
    )?;
    let forward_fat_pointer = UInt8::equals(
        cs,
        &forwarding_mode_byte,
        &UInt8::<E>::from_uint(RetForwardPageType::ForwardFatPointer as u8),
    )?;
    let use_heap = smart_and(cs, &[use_aux_heap.not(), forward_fat_pointer.not()])?;

    // now we can parse and validate fat pointer
    let (fat_ptr, upper_bound, ptr_validation_exception, out_of_bounds) =
        FatPtrInABI::parse_and_validate(cs, input, forward_fat_pointer.not(), optimizer)?;

    let flags = CommonABIFlags {
        use_heap,
        use_aux_heap,
        forward_fat_pointer,
    };

    let validation_data = FatPtrValidationData {
        invalid: ptr_validation_exception,
        memory_is_not_addressable: out_of_bounds,
        upper_bound,
    };

    Ok((fat_ptr, flags, validation_data))
}

fn callstack_candidate_for_ret<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    opcode_carry_parts: &OpcodeCarryParts<E>,
    optimizer: &mut OptimizationContext<E>,
    witness_oracle: &mut impl WitnessOracle<E>,
    fat_ptr: &FatPtrInABI<E>,
    common_abi_flags: &CommonABIFlags,
    pointer_validation_data: &FatPtrValidationData<E>,
) -> Result<RetData<E>, SynthesisError> {
    // new callstack should be just the same a the old one, but we also need to update the pricing for pubdata in the rare case
    let opcode = zkevm_opcode_defs::Opcode::Ret(zkevm_opcode_defs::RetOpcode::Ok);
    let marker = opcode.variant_idx() as u64;
    let execute = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(opcode);
    let is_ret_ok = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(zkevm_opcode_defs::Opcode::Ret(
            zkevm_opcode_defs::RetOpcode::Ok,
        ));
    // revert and panic are different only in ABI: whether we zero-out any hints (returndata) about why we reverted or not
    let is_ret_revert = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(zkevm_opcode_defs::Opcode::Ret(
            zkevm_opcode_defs::RetOpcode::Revert,
        ));
    let is_ret_panic = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(zkevm_opcode_defs::Opcode::Ret(
            zkevm_opcode_defs::RetOpcode::Panic,
        ));

    let is_local_frame = current_state
        .callstack
        .current_context
        .saved_context
        .extension
        .is_local_call;
    let current_callstack_entry = current_state
        .callstack
        .current_context
        .saved_context
        .clone();

    // we may want to return to label
    let is_to_label = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[zkevm_opcode_defs::ret::RET_TO_LABEL_BIT_IDX];
    let label_pc = common_opcode_state.decoded_opcode.imm0;

    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        let ret_type = if is_ret_ok.get_value().unwrap_or(false) {
            "OK"
        } else if is_ret_revert.get_value().unwrap_or(false) {
            "REVERT"
        } else if is_ret_panic.get_value().unwrap_or(false) {
            "PANIC"
        } else {
            ""
        };
        if is_local_frame.get_value().is_some() {
            if is_local_frame.get_value().unwrap() {
                println!("Executing LOCAL RET {}", ret_type);
            } else {
                println!("Executing FAR RET {}", ret_type);
            }
        }
    }

    let current_depth = current_state.callstack.context_stack_depth;
    let (new_callstack_entry_witness, callstack_state_witness) =
        witness_oracle.get_callstack_witness(&execute, &current_depth);

    let previous_callstack_state = Num::alloc_multiple(cs, callstack_state_witness)?;

    let mut new_callstack_entry =
        ExecutionContextRecord::allocate_in_optimization_context_with_applicability(
            cs,
            new_callstack_entry_witness,
            optimizer,
            &execute,
            CtxMarker::from(marker as u8),
        )?;

    let originally_popped_context = new_callstack_entry.clone();

    // pass back all the ergs (after we paid the cost of "ret" itself),
    // with may be a small charge for memory growth
    let preliminary_ergs_left = common_opcode_state.preliminary_ergs_left;

    // resolve some exceptions over fat pointer use and memory growth

    // exceptions that are specific only to return from non-local frame
    let mut non_local_frame_exceptions = vec![];

    if crate::VERBOSE_CIRCUITS && execute.get_value().unwrap_or(false) {
        if common_abi_flags
            .forward_fat_pointer
            .get_value()
            .unwrap_or(false)
        {
            println!(
                "Forwarding fat pointer {:?} on return",
                fat_ptr.create_witness().unwrap()
            );
        }
    }

    // resolve returndata pointer if forwarded
    let fat_ptr_expected_exception = smart_and(
        cs,
        &[
            common_abi_flags.forward_fat_pointer,
            common_opcode_state.src0_view.is_ptr.not(),
            is_local_frame.not(),
        ],
    )?;
    non_local_frame_exceptions.push(fat_ptr_expected_exception);

    non_local_frame_exceptions.push(pointer_validation_data.invalid);

    let fat_ptr = fat_ptr.clone();

    // we also want unidirectional movement of returndata
    // check if fat_ptr.memory_page < ctx.base_page and throw if it's the case
    let (_, uf) = fat_ptr.page.sub_using_delayed_bool_allocation(
        cs,
        &current_state
            .callstack
            .current_context
            .saved_context
            .common_part
            .base_page,
        optimizer,
    )?;

    // if we try to forward then we should be unidirectional
    let non_unidirectional_forwarding = smart_and(cs, &[common_abi_flags.forward_fat_pointer, uf])?;

    non_local_frame_exceptions.push(non_unidirectional_forwarding);

    non_local_frame_exceptions.push(is_ret_panic); // just feed it here as a shorthand

    let exceptions_collapsed = smart_or(cs, &non_local_frame_exceptions)?;

    let fat_ptr = fat_ptr.mask_into_empty(cs, exceptions_collapsed)?;

    // now we can modify fat ptr that is prevalidated

    let fat_ptr_adjusted_if_forward = fat_ptr.readjust(cs, optimizer)?;

    let page = UInt32::conditionally_select(
        cs,
        &common_abi_flags.use_heap,
        &opcode_carry_parts.heap_page,
        &opcode_carry_parts.aux_heap_page,
    )?;

    let fat_ptr_for_heaps = FatPtrInABI {
        offset: UInt32::zero(),
        page,
        start: fat_ptr.start,
        length: fat_ptr.length,
    };

    let fat_ptr = FatPtrInABI::conditionally_select(
        cs,
        &common_abi_flags.forward_fat_pointer,
        &fat_ptr_adjusted_if_forward,
        &fat_ptr_for_heaps,
    )?;

    // potentially pay for memory growth
    let upper_bound = pointer_validation_data.upper_bound;
    // mask into 0 if we are executing "panic" due to exceptions
    let upper_bound = upper_bound.mask(cs, &exceptions_collapsed.not())?;
    let penalize_for_out_of_bounds = pointer_validation_data.memory_is_not_addressable;
    let upper_bound = UInt32::conditionally_select(
        cs,
        &penalize_for_out_of_bounds,
        &UInt32::from_uint(u32::MAX),
        &upper_bound,
    )?;

    let heap_max_accessed = upper_bound.mask(cs, &common_abi_flags.use_heap)?;
    let heap_bound = current_callstack_entry.common_part.heap_upper_bound;
    let (mut heap_growth, uf) =
        heap_max_accessed.sub_using_delayed_bool_allocation(cs, &heap_bound, optimizer)?;
    heap_growth = heap_growth.mask(cs, &uf.not())?; // of we access in bounds then it's 0
    let grow_heap = smart_and(
        cs,
        &[common_abi_flags.use_heap, execute, is_local_frame.not()],
    )?;

    let aux_heap_max_accessed = upper_bound.mask(cs, &common_abi_flags.use_aux_heap)?;
    let aux_heap_bound = current_callstack_entry.common_part.aux_heap_upper_bound;
    let (mut aux_heap_growth, uf) =
        aux_heap_max_accessed.sub_using_delayed_bool_allocation(cs, &aux_heap_bound, optimizer)?;
    aux_heap_growth = aux_heap_growth.mask(cs, &uf.not())?; // of we access in bounds then it's 0
    let grow_aux_heap = smart_and(
        cs,
        &[common_abi_flags.use_aux_heap, execute, is_local_frame.not()],
    )?;

    let mut growth_cost =
        UInt32::conditionally_select(cs, &grow_heap, &heap_growth, &UInt32::zero())?;

    growth_cost = UInt32::conditionally_select(cs, &grow_aux_heap, &aux_heap_growth, &growth_cost)?;

    let (ergs_left_after_growth, uf) =
        preliminary_ergs_left.sub_using_delayed_bool_allocation(cs, &growth_cost, optimizer)?;

    let mut non_local_frame_exceptions = vec![];
    non_local_frame_exceptions.push(exceptions_collapsed);

    let ergs_left_after_growth = ergs_left_after_growth.mask(cs, &uf.not())?; // if not enough - set to 0
    non_local_frame_exceptions.push(uf);

    let ergs_left_after_growth = UInt32::conditionally_select(
        cs,
        &is_local_frame,
        &preliminary_ergs_left,
        &ergs_left_after_growth,
    )?;

    non_local_frame_exceptions.push(is_ret_panic);

    let non_local_frame_panic = smart_or(cs, &non_local_frame_exceptions)?;
    let non_local_frame_panic = smart_and(cs, &[non_local_frame_panic, is_local_frame.not()])?;
    let final_fat_ptr = fat_ptr.mask_into_empty(cs, non_local_frame_panic)?;

    // -----------------------------------------

    let (new_ergs_left, _) = ergs_left_after_growth.add_using_delayed_bool_allocation(
        cs,
        &new_callstack_entry.common_part.ergs_remaining,
        optimizer,
    )?;

    new_callstack_entry.common_part.ergs_remaining = new_ergs_left;

    // resolve merging of the queues

    // most likely it's the most interesting amount all the tricks that are pulled by this VM

    // During the execution we maintain the following queue segments of what is usually called a "storage log", that is basically a sequence of bookkeeped
    // storage, events, precompiles, etc accesses
    // - global "forward" queue - all the changes (both rollbackable and not (read-like)) go in there, and it's "global" per block
    // - frame-specific "reverts" queue, where we put "canceling" state updates for all "write-like" things, like storage write, event,
    // l1 message, etc. E.g. precompilecall is pure function and doesn't rollback, and we add nothing to this segment
    // When frame ends we have to decide whether we discard it's changes or not. So we can do either:
    // - if frame does NOT revert then we PREPEND all the changes in "rollback" segment to the rollback segment of the parent queue
    // - if frame DOES revert, then we APPEND all the changes from "rollback" to the global "forward" segment
    // It's easy to notice that this behavior is:
    // - local O(1): only things like heads/tails of the queues are updated. Changes do accumulate along the O(N) potential changes in a frame, but
    // then we can apply it O(1)
    // - recursively consistent as one would expect it: if this frame does NOT revert, but parent REVERTS, then all the changes are rolled back!

    // Why one can not do simpler and just memorize the state of some "forward" queue on frame entry and return to it when revert happens? Because we can have
    // a code like
    // if (SLOAD(x)) {
    //     revert(0, 0)
    // } else {
    //     .. something useful
    // }

    // then we branch on result of SLOAD, but it is not observable (we discarded everything in "forward" queue)! So it can be maliciously manipulated!

    // if we revert then we should append rollback to forward
    // if we return ok then we should prepend to the rollback of the parent

    let should_perform_revert =
        smart_or(cs, &[is_ret_revert, is_ret_panic, non_local_frame_panic])?;
    let perform_revert = smart_and(cs, &[execute, should_perform_revert])?;

    Num::conditionally_enforce_equal(
        cs,
        &perform_revert,
        &current_callstack_entry.common_part.reverted_queue_head,
        &current_state
            .callstack
            .current_context
            .log_queue_forward_tail,
    )?;

    let (new_forward_queue_len_if_revert, _) = current_state
        .callstack
        .current_context
        .log_queue_forward_part_length
        .add_using_delayed_bool_allocation(
            cs,
            &current_callstack_entry
                .common_part
                .reverted_queue_segment_len,
            optimizer,
        )?;

    let should_perform_ret_ok = smart_and(cs, &[execute, is_ret_ok, non_local_frame_panic.not()])?;

    Num::conditionally_enforce_equal(
        cs,
        &should_perform_ret_ok,
        &new_callstack_entry.common_part.reverted_queue_head,
        &current_callstack_entry.common_part.reverted_queue_tail,
    )?;

    let (new_rollback_queue_len_if_ok, _) = new_callstack_entry
        .common_part
        .reverted_queue_segment_len
        .add_using_delayed_bool_allocation(
            cs,
            &current_callstack_entry
                .common_part
                .reverted_queue_segment_len,
            optimizer,
        )?;

    // update forward queue

    let new_forward_queue_state = Num::conditionally_select(
        cs,
        &should_perform_revert, // it's only true if we DO execute and DO revert
        &current_callstack_entry.common_part.reverted_queue_tail,
        &current_state
            .callstack
            .current_context
            .log_queue_forward_tail,
    )?;

    let new_forward_queue_len = UInt32::conditionally_select(
        cs,
        &should_perform_revert,
        &new_forward_queue_len_if_revert,
        &current_state
            .callstack
            .current_context
            .log_queue_forward_part_length,
    )?;

    // update rollback queue of the parent
    let new_rollback_queue_head = Num::conditionally_select(
        cs,
        &should_perform_ret_ok, // it's only true if we DO execute and DO return ok
        &current_callstack_entry.common_part.reverted_queue_head,
        &new_callstack_entry.common_part.reverted_queue_head,
    )?;

    let new_rollback_queue_len = UInt32::conditionally_select(
        cs,
        &should_perform_ret_ok,
        &new_rollback_queue_len_if_ok,
        &new_callstack_entry.common_part.reverted_queue_segment_len,
    )?;

    new_callstack_entry.common_part.reverted_queue_head = new_rollback_queue_head;
    new_callstack_entry.common_part.reverted_queue_segment_len = new_rollback_queue_len;

    // we ignore label if we return from the root, of course
    let should_use_label = smart_and(cs, &[is_to_label, is_local_frame])?;

    // Candidates for PC to return to
    let ok_ret_pc = UInt16::conditionally_select(
        cs,
        &should_use_label,
        &label_pc,
        &new_callstack_entry.common_part.pc,
    )?;
    // but EH is stored in the CURRENT context
    let eh_pc = UInt16::conditionally_select(
        cs,
        &should_use_label,
        &label_pc,
        &current_callstack_entry.common_part.exception_handler_loc,
    )?;

    let dst_pc = UInt16::conditionally_select(cs, &perform_revert, &eh_pc, &ok_ret_pc)?;

    new_callstack_entry.common_part.pc = dst_pc;

    // and update registers following our ABI rules

    // everything goes into r1, and the rest is cleared
    let new_r1 = final_fat_ptr.into_register(cs)?;
    let update_specific_registers_on_ret = smart_and(cs, &[execute, is_local_frame.not()])?;

    let updated_registers = vec![(0, new_r1)];

    let is_panic = smart_or(cs, &[is_ret_panic, non_local_frame_panic])?;

    // the rest is cleared

    let mut register_cleanups = Vec::with_capacity(16);
    for reg_idx in 1..REGISTERS_COUNT {
        register_cleanups.push((update_specific_registers_on_ret, reg_idx));
    }

    // erase markers everywhere anyway
    let mut erase_ptr_markers = Vec::with_capacity(16);
    for reg_idx in 1..REGISTERS_COUNT {
        erase_ptr_markers.push((update_specific_registers_on_ret, reg_idx));
    }

    assert_eq!(register_cleanups.len(), erase_ptr_markers.len());

    // if we didn't decommit for ANY reason then we will have target memory page == UNMAPPED PAGE, that will trigger panic
    let full_data = RetData {
        applies: execute,
        new_context: new_callstack_entry,
        originally_popped_context,
        previous_callstack_state,
        new_forward_queue_state,
        new_forward_queue_len,
        updated_registers: updated_registers,
        did_return_from_far_call: is_local_frame.not(),
        is_panic: is_panic,
        update_specific_registers_on_ret,
        zero_out_specific_registers: register_cleanups,
        remove_ptr_on_specific_registers: erase_ptr_markers,
    };

    Ok(full_data)
}
