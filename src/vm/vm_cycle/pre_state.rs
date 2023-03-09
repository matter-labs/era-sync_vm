use super::*;

use super::super::vm_state::VmLocalState;
use crate::vm::primitives::register_view::*;
use crate::vm::vm_cycle::opcode_bitmask::SUPPORTED_ISA_VERSION;
use crate::vm::vm_cycle::witness_oracle::WitnessOracle;
use crate::vm::vm_state::callstack::Callstack;
use cs_derive::*;
use zkevm_opcode_defs::NopOpcode;

use crate::vm::helpers::skip_cycle::*;

pub fn create_prestate<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: VmLocalState<E, 3>,
    witness_oracle: &mut impl WitnessOracle<E>,
    round_function: &R,
) -> Result<
    (
        VmLocalState<E, 3>,
        CommonOpcodeState<E>,
        OpcodeCarryParts<E>,
    ),
    SynthesisError,
> {
    // println!("NEW CYCLE -------------- PRESTATE");
    let n = cs.get_current_aux_gate_number();

    let mut current_state = current_state;
    let mut optimizer = OptimizationContext::empty();

    let execution_has_ended = current_state.callstack.is_empty(cs)?;
    let is_any_pending = current_state.pending_sponges.is_any_pending(cs)?;
    let should_skip_cycle = smart_or(cs, &[execution_has_ended, is_any_pending])?;
    let pending_exception = current_state.pending_exception;

    if crate::VERBOSE_CIRCUITS {
        println!("New cycle");
    }

    if crate::VERBOSE_CIRCUITS && should_skip_cycle.get_value().unwrap_or(false) {
        println!("Skipping cycle");
        if is_any_pending.get_value().unwrap_or(false) {
            println!("Skip from pending");
        }
    }

    // we should even try to perform a read only if we have something to do this cycle. So We should not skip
    // cycle or have some pending operation
    let should_try_to_read_opcode =
        smart_and(cs, &[should_skip_cycle.not(), pending_exception.not()])?;
    let execute_pending_exception_at_this_cycle =
        smart_and(cs, &[should_skip_cycle.not(), pending_exception])?;

    if crate::VERBOSE_CIRCUITS
        && execute_pending_exception_at_this_cycle
            .get_value()
            .unwrap_or(false)
    {
        println!("Execute pending exception cycle");
    }

    current_state.pending_exception = Boolean::conditionally_select(
        cs,
        &execute_pending_exception_at_this_cycle,
        &Boolean::constant(false),
        &current_state.pending_exception,
    )?;

    let current_pc = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .pc;

    let (pc_plus_one, _) =
        current_pc.add_using_delayed_bool_allocation(cs, &UInt16::from_uint(1), &mut optimizer)?;
    let (super_pc, subpc_spread) = split_pc(cs, current_pc)?;
    let previous_super_pc = current_state.previous_super_pc;

    let should_read_for_new_pc = should_read_memory(
        cs,
        current_state.did_call_or_ret_recently,
        super_pc,
        previous_super_pc,
    )?;

    let should_read_opcode = smart_and(cs, &[should_try_to_read_opcode, should_read_for_new_pc])?;

    // if we did skip cycle then do NOT reset it, even though we formally NOP. Then opcodes will actually set if
    // if they are not NOP
    current_state.did_call_or_ret_recently = Boolean::conditionally_select(
        cs,
        &should_skip_cycle,
        &current_state.did_call_or_ret_recently,
        &Boolean::constant(false),
    )?;
    // and in addition if we did finish execution then we never care and cleanup
    current_state.did_call_or_ret_recently = Boolean::conditionally_select(
        cs,
        &execution_has_ended,
        &Boolean::constant(false),
        &current_state.did_call_or_ret_recently,
    )?;

    use crate::vm::vm_cycle::memory::MemoryLocation;
    let location = MemoryLocation {
        page: current_state
            .callstack
            .current_context
            .saved_context
            .common_part
            .code_page,
        index: UInt32::from_num_unchecked(super_pc.inner),
    };

    // precompute timestamps
    let timestamp_for_code_or_src_read = current_state.timestamp;
    let timestamp_for_first_decommit_or_precompile_read =
        timestamp_for_code_or_src_read.increment_unchecked(cs)?;
    let timestamp_for_second_decommit_or_precompile_write =
        timestamp_for_first_decommit_or_precompile_read.increment_unchecked(cs)?;
    let timestamp_for_dst_write =
        timestamp_for_second_decommit_or_precompile_write.increment_unchecked(cs)?;
    let next_cycle_timestamp = timestamp_for_dst_write.increment_unchecked(cs)?;
    let next_cycle_timestamp = UInt32::conditionally_select(
        cs,
        &should_skip_cycle,
        &current_state.timestamp,
        &next_cycle_timestamp,
    )?;

    use crate::vm::vm_cycle::memory::may_be_read_memory_for_code;

    let (
        mut code_words,
        (
            initial_state_sponge_0,
            final_state_sponge_0,
            new_memory_queue_length,
            should_use_sponge_0,
        ),
    ) = may_be_read_memory_for_code(
        cs,
        should_read_opcode,
        timestamp_for_code_or_src_read,
        location,
        current_state.memory_queue_state,
        current_state.memory_queue_length,
        round_function,
        witness_oracle,
    )?;

    // update current state
    current_state.memory_queue_length = new_memory_queue_length;
    current_state.memory_queue_state = final_state_sponge_0;

    for (dst, src) in code_words
        .iter_mut()
        .zip(current_state.previous_code_word.iter())
    {
        *dst = UInt64::conditionally_select(cs, &should_read_opcode, &dst, src)?;
    }

    use crate::vm::vm_cycle::initial_decoding::spread_into_bits;
    // subpc is 2 bits, so it's a range from 0 to 3. 1..=3 are bitspread via the table
    let subpc_bitmask = spread_into_bits::<_, _, 3>(cs, subpc_spread, &mut optimizer)?;

    // default one is one corresponding to the "highest" bytes in 32 byte word in our BE machine
    let opcode = code_words[3];

    // and select for subpc being 1..=3
    let opcode = UInt64::conditionally_select(cs, &subpc_bitmask[0], &code_words[2], &opcode)?;

    let opcode = UInt64::conditionally_select(cs, &subpc_bitmask[1], &code_words[1], &opcode)?;

    let opcode = UInt64::conditionally_select(cs, &subpc_bitmask[2], &code_words[0], &opcode)?;

    // mask if we would be ok with NOPing. This masks a full 8-byte opcode, and not properties bitspread
    // We mask if this cycle is just NOPing till the end of circuit
    let opcode = mask_into_nop(cs, &should_skip_cycle, opcode)?;
    // if we are not pending, and we have an exception to run - run it
    let opcode = mask_into_panic(cs, &execute_pending_exception_at_this_cycle, opcode)?;

    // update super_pc and code words if we did read
    current_state.previous_code_word = code_words;
    current_state.previous_super_pc = UInt16::conditionally_select(
        cs,
        &should_skip_cycle.not(),
        &super_pc,
        &current_state.previous_super_pc,
    )?; // may be it can be unconditional

    let is_kernel_mode = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .is_kernel_mode;
    let is_static_context = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .is_static_execution;
    let callstack_is_full = current_state.callstack.is_full(cs)?;
    let ergs_left = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .ergs_remaining;
    use crate::vm::helpers::opcode::encode_flags;
    let encoded_flags = encode_flags(cs, &current_state.flags)?;

    use crate::vm::helpers::opcode::partially_decode_from_uint64_and_resolve_condition;
    use crate::vm::vm_cycle::initial_decoding::perform_initial_decoding;
    let (decoded_opcode, dirty_ergs_left) = perform_initial_decoding(
        cs,
        opcode,
        encoded_flags,
        is_kernel_mode,
        is_static_context,
        callstack_is_full,
        ergs_left,
        should_skip_cycle,
        &mut optimizer,
    )?;

    // decoded opcode and current (yet dirty) ergs left should be passed into the opcode

    // we did all the masking and "INVALID" opcode must never happed
    let invalid_opcode_bit =
        decoded_opcode
            .properties_bits
            .boolean_for_opcode(zkevm_opcode_defs::Opcode::Invalid(
                zkevm_opcode_defs::InvalidOpcode,
            ));

    Boolean::enforce_equal(cs, &invalid_opcode_bit, &Boolean::constant(false))?;

    // now read source operands
    // select low part of the registers
    let mut draft_src0 = Register::<E>::zero();
    for (mask_bit, register) in decoded_opcode.src_regs_selectors[0]
        .iter()
        .zip(current_state.registers.iter())
    {
        draft_src0 = Register::conditionally_select(cs, mask_bit, &register, &draft_src0)?;
    }
    let src0_reg_lowest = draft_src0.inner[0].decompose_into_uint16_in_place(cs)?;
    let src0_reg_lowest = src0_reg_lowest[0];

    let mut src1_register = Register::<E>::zero();
    for (mask_bit, register) in decoded_opcode.src_regs_selectors[1]
        .iter()
        .zip(current_state.registers.iter())
    {
        src1_register = Register::conditionally_select(cs, mask_bit, &register, &src1_register)?;
    }

    let mut current_dst0_reg_low = UInt128::<E>::zero();
    for (mask_bit, register) in decoded_opcode.dst_regs_selectors[0]
        .iter()
        .zip(current_state.registers.iter())
    {
        let reg_low = register.inner[0];
        current_dst0_reg_low =
            UInt128::conditionally_select(cs, mask_bit, &reg_low, &current_dst0_reg_low)?;
    }
    let dst0_reg_lowest = current_dst0_reg_low.decompose_into_uint16_in_place(cs)?;
    let dst0_reg_lowest = dst0_reg_lowest[0];

    let current_sp = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .sp;
    let code_page = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .code_page;
    let base_page = current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .base_page;
    let stack_page = base_page.increment_unchecked(cs)?;
    let heap_page = stack_page.increment_unchecked(cs)?;
    let aux_heap_page = heap_page.increment_unchecked(cs)?;
    use crate::vm::vm_cycle::memory::*;

    let (memory_location_for_src0, new_sp_after_src0, should_read_memory_for_src0) =
        resolve_memory_region_and_index_for_source(
            cs,
            code_page,
            stack_page,
            src0_reg_lowest,
            &decoded_opcode,
            &mut optimizer,
            current_sp,
        )?;

    let (memory_location_for_dst0, new_sp, should_write_memory_for_dst0) =
        resolve_memory_region_and_index_for_dest(
            cs,
            stack_page,
            dst0_reg_lowest,
            &decoded_opcode,
            &mut optimizer,
            new_sp_after_src0,
        )?;

    current_state
        .callstack
        .current_context
        .saved_context
        .common_part
        .sp = new_sp;

    // perform actual read

    use crate::vm::vm_cycle::memory::may_be_read_memory_for_source_operand;
    let (
        src0_register_from_mem,
        (
            initial_state_sponge_1,
            final_state_sponge_1,
            new_memory_queue_length,
            should_use_sponge_1,
        ),
    ) = may_be_read_memory_for_source_operand(
        cs,
        should_read_memory_for_src0,
        timestamp_for_code_or_src_read,
        memory_location_for_src0,
        current_state.memory_queue_state,
        current_state.memory_queue_length,
        round_function,
        witness_oracle,
    )?;

    // update current state
    current_state.memory_queue_length = new_memory_queue_length;
    current_state.memory_queue_state = final_state_sponge_1;

    // select source0 and source1

    use zkevm_opcode_defs::ImmMemHandlerFlags;

    // select if it was reg
    let src0 = Register::conditionally_select(
        cs,
        &decoded_opcode
            .properties_bits
            .boolean_for_src_mem_access(ImmMemHandlerFlags::UseRegOnly),
        &draft_src0,
        &src0_register_from_mem,
    )?;

    let imm_as_reg = Register::from_imm(decoded_opcode.imm0);
    // select if it was imm
    let src0 = Register::conditionally_select(
        cs,
        &decoded_opcode
            .properties_bits
            .boolean_for_src_mem_access(ImmMemHandlerFlags::UseImm16Only),
        &imm_as_reg,
        &src0,
    )?;

    // form an intermediate state to process the opcodes over it
    let (next_pc, _) =
        current_pc.add_using_delayed_bool_allocation(cs, &UInt16::from_uint(1), &mut optimizer)?;

    // swap operands
    let swap_operands = {
        // Opcode::Sub(_) | Opcode::Div(_) | Opcode::Shift(_) => self.flags[SWAP_OPERANDS_FLAG_IDX],

        use zkevm_opcode_defs::*;

        let is_sub = decoded_opcode
            .properties_bits
            .boolean_for_opcode(Opcode::Sub(SubOpcode::Sub));
        let is_div = decoded_opcode
            .properties_bits
            .boolean_for_opcode(Opcode::Div(DivOpcode));
        let is_shift = decoded_opcode
            .properties_bits
            .boolean_for_opcode(Opcode::Shift(ShiftOpcode::Rol));

        let is_assymmetric = smart_or(cs, &[is_sub, is_div, is_shift])?;
        let swap_flag =
            decoded_opcode.properties_bits.flag_booleans[SWAP_OPERANDS_FLAG_IDX_FOR_ARITH_OPCODES];

        let t0 = smart_and(cs, &[is_assymmetric, swap_flag])?;

        let is_ptr = decoded_opcode
            .properties_bits
            .boolean_for_opcode(Opcode::Ptr(PtrOpcode::Add));
        let swap_flag =
            decoded_opcode.properties_bits.flag_booleans[SWAP_OPERANDS_FLAG_IDX_FOR_PTR_OPCODE];

        let t1 = smart_and(cs, &[is_ptr, swap_flag])?;

        smart_or(cs, &[t0, t1])?
    };

    let (src0, src1) = Register::conditionally_reverse(cs, &swap_operands, &src0, &src1_register)?;

    // constraint everything in optimizer
    optimizer.enforce_boolean_allocations(cs)?;
    drop(optimizer);

    let src0_view = RegisterInputView::from_input_value(cs, &src0)?;
    let src1_view = RegisterInputView::from_input_value(cs, &src1)?;

    let common_opcode_state = CommonOpcodeState {
        reseted_flags: ArithmeticFlagsPort::reseted_flags(),
        current_flags: current_state.flags,
        decoded_opcode: decoded_opcode.clone(),
        src0,
        src1,
        src0_view,
        src1_view,
        next_pc,
        is_kernel_mode,
        preliminary_ergs_left: dirty_ergs_left,
        timestamp_for_code_or_src_read,
        timestamp_for_first_decommit_or_precompile_read,
        timestamp_for_second_decommit_or_precompile_write,
        timestamp_for_dst_write,
    };

    let carry_parts = OpcodeCarryParts {
        did_skip_cycle: should_skip_cycle,
        opcode_read_sponge_data: PendingRecord {
            initial_state: initial_state_sponge_0,
            final_state: final_state_sponge_0,
            is_used: should_use_sponge_0,
        },
        src0_read_sponge_data: PendingRecord {
            initial_state: initial_state_sponge_1,
            final_state: final_state_sponge_1,
            is_used: should_use_sponge_1,
        },
        decoded_opcode,
        dst0_memory_location: memory_location_for_dst0,
        dst0_performs_memory_access: should_write_memory_for_dst0,
        timestamp_for_code_or_src_read,
        timestamp_for_first_decommit_or_precompile_read,
        timestamp_for_second_decommit_or_precompile_write,
        timestamp_for_dst_write,
        next_cycle_timestamp,
        preliminary_ergs_left: dirty_ergs_left,
        pc_plus_one,
        heap_page,
        aux_heap_page,
    };

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used to create pre-state", gates_used);
    // dbg!(_message);

    Ok((current_state, common_opcode_state, carry_parts))
}

use crate::vm::ports::ArithmeticFlagsPort;
use crate::vm::vm_cycle::initial_decoding::OpcodeFinalDecoding;
use crate::vm::vm_state::PendingRecord;

pub struct CommonOpcodeState<E: Engine> {
    pub reseted_flags: ArithmeticFlagsPort<E>,
    pub current_flags: ArithmeticFlagsPort<E>,
    pub decoded_opcode: OpcodeFinalDecoding<E>,
    pub src0: Register<E>,
    pub src1: Register<E>,
    pub src0_view: RegisterInputView<E>,
    pub src1_view: RegisterInputView<E>,
    pub next_pc: UInt16<E>,
    pub is_kernel_mode: Boolean,
    pub preliminary_ergs_left: UInt32<E>,
    pub timestamp_for_code_or_src_read: UInt32<E>,
    pub timestamp_for_first_decommit_or_precompile_read: UInt32<E>,
    pub timestamp_for_second_decommit_or_precompile_write: UInt32<E>,
    pub timestamp_for_dst_write: UInt32<E>,
}

use crate::vm::vm_cycle::memory::MemoryLocation;

pub struct OpcodeCarryParts<E: Engine> {
    pub did_skip_cycle: Boolean,
    pub opcode_read_sponge_data: PendingRecord<E, 3>,
    pub src0_read_sponge_data: PendingRecord<E, 3>,
    pub timestamp_for_code_or_src_read: UInt32<E>,
    pub timestamp_for_first_decommit_or_precompile_read: UInt32<E>,
    pub timestamp_for_second_decommit_or_precompile_write: UInt32<E>,
    pub timestamp_for_dst_write: UInt32<E>,
    pub heap_page: UInt32<E>,
    pub aux_heap_page: UInt32<E>,
    pub next_cycle_timestamp: UInt32<E>,
    pub preliminary_ergs_left: UInt32<E>,
    pub decoded_opcode: OpcodeFinalDecoding<E>,
    pub dst0_memory_location: MemoryLocation<E>,
    pub dst0_performs_memory_access: Boolean,
    pub pc_plus_one: UInt16<E>,
}

use zkevm_opcode_defs::ISAVersion;

pub trait PartialOpcodePropsMarker: Clone + std::fmt::Debug {
    fn can_have_src0_from_mem(&self, version: ISAVersion) -> bool;
    fn can_write_dst0_into_memory(&self, version: ISAVersion) -> bool;
    fn default() -> Self;
}

impl PartialOpcodePropsMarker for zkevm_opcode_defs::Opcode {
    fn can_have_src0_from_mem(&self, version: ISAVersion) -> bool {
        zkevm_opcode_defs::Opcode::can_have_src0_from_mem(self, version)
    }

    fn can_write_dst0_into_memory(&self, version: ISAVersion) -> bool {
        zkevm_opcode_defs::Opcode::can_write_dst0_into_memory(self, version)
    }

    fn default() -> Self {
        zkevm_opcode_defs::Opcode::Invalid(zkevm_opcode_defs::definitions::InvalidOpcode)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum SpecializedImplementationPropsMarker {
    CallRet(
        zkevm_opcode_defs::NearCallOpcode,
        zkevm_opcode_defs::FarCallOpcode,
        zkevm_opcode_defs::RetOpcode,
    ),
}

#[derive(Clone, Copy, Debug)]
pub enum PropsMarker {
    Normal(zkevm_opcode_defs::Opcode),
    Specialized(SpecializedImplementationPropsMarker),
}

impl PartialOpcodePropsMarker for PropsMarker {
    fn can_have_src0_from_mem(&self, version: ISAVersion) -> bool {
        match self {
            PropsMarker::Normal(sub) => sub.can_have_src0_from_mem(version),
            PropsMarker::Specialized(sub) => sub.can_have_src0_from_mem(version),
        }
    }

    fn can_write_dst0_into_memory(&self, version: ISAVersion) -> bool {
        match self {
            PropsMarker::Normal(sub) => sub.can_write_dst0_into_memory(version),
            PropsMarker::Specialized(sub) => sub.can_write_dst0_into_memory(version),
        }
    }

    fn default() -> Self {
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Nop(NopOpcode))
    }
}

pub const NUM_MARKER_BRANCHES: usize = 13;
pub const ALL_OPCODE_MARKERS: [PropsMarker; NUM_MARKER_BRANCHES] = all_markers();

pub const fn all_markers() -> [PropsMarker; NUM_MARKER_BRANCHES] {
    use zkevm_opcode_defs::*;

    [
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Nop(NopOpcode)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Add(AddOpcode::Add)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Sub(SubOpcode::Sub)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Mul(MulOpcode)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Div(DivOpcode)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Jump(JumpOpcode)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Ptr(PtrOpcode::Add)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Context(ContextOpcode::Caller)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Shift(ShiftOpcode::Shl)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Binop(BinopOpcode::Xor)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::Log(LogOpcode::StorageRead)),
        PropsMarker::Normal(zkevm_opcode_defs::Opcode::UMA(UMAOpcode::HeapRead)),
        PropsMarker::Specialized(SpecializedImplementationPropsMarker::CallRet(
            zkevm_opcode_defs::NearCallOpcode,
            zkevm_opcode_defs::FarCallOpcode::Normal,
            zkevm_opcode_defs::RetOpcode::Ok,
        )),
    ]
}

impl PartialOpcodePropsMarker for SpecializedImplementationPropsMarker {
    fn can_have_src0_from_mem(&self, version: ISAVersion) -> bool {
        use zkevm_opcode_defs::OpcodeProps;

        let t0 = zkevm_opcode_defs::NearCallOpcode.can_have_src0_from_mem(version);
        let t1 = zkevm_opcode_defs::FarCallOpcode::Normal.can_have_src0_from_mem(version);
        let t2 = zkevm_opcode_defs::RetOpcode::Ok.can_have_src0_from_mem(version);
        assert_eq!(t0, t1);
        assert_eq!(t0, t2);

        t0
    }

    fn can_write_dst0_into_memory(&self, version: ISAVersion) -> bool {
        use zkevm_opcode_defs::OpcodeProps;

        let t0 = zkevm_opcode_defs::NearCallOpcode.can_write_dst0_into_memory(version);
        let t1 = zkevm_opcode_defs::FarCallOpcode::Normal.can_write_dst0_into_memory(version);
        let t2 = zkevm_opcode_defs::RetOpcode::Ok.can_write_dst0_into_memory(version);
        assert_eq!(t0, t1);
        assert_eq!(t0, t2);

        t0
    }

    fn default() -> Self {
        unimplemented!();
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub enum PendingArithmeticRelation<E: Engine> {
    AddSubRelation(AddSubRelationship<E>),
    MulDivRelation(MulDivRelationship<E>),
    RangeCheckRelation((Num<E>, usize)),
}

// Explicitly unrolled set of differences that individual opcodes can bring

pub struct OpcodePartialApplicationResult<E: Engine, M: PartialOpcodePropsMarker> {
    pub marker: M,
    pub applies: Boolean, // we should support specialized implementations, so marker is explicit
    pub pending_sponges: Vec<PendingRecord<E, 3>>, // all desired SPECIFIC sponges, will resolve later
    pub dst0_value: Option<(Boolean, Register<E>)>, // not every opcode has to write in it, and some opcodes may or may not update out0
    pub dst1_value: Option<(Boolean, Register<E>)>, // not every opcode has to write in it
    pub flags: Vec<(Boolean, ArithmeticFlagsPort<E>)>,
    pub specific_registers_updates: Vec<(usize, Boolean, Register<E>)>, // MUST BE ORDERED. Mainly for far_call/ret ABI
    pub zero_out_specific_registers: Vec<(Boolean, usize)>,             // MUST BE ORDERED
    pub remove_ptr_on_specific_registers: Vec<(Boolean, usize)>,        // MUST BE ORDERED
    pub pending_exception: Option<Boolean>,
    pub callstack: Option<Callstack<E, 3>>, // ideally resolve near_call/far_call/ret all together
    pub ergs_left: Option<UInt32<E>>, // should not be set if not used, even though we can use CircuitEq
    pub new_pc: Option<UInt16<E>>,    // should not be set if not used (PC+1 is set by default)
    pub new_ergs_per_pubdata_byte: Option<(Boolean, UInt32<E>)>,
    pub new_tx_number_in_block: Option<(Boolean, UInt16<E>)>,
    pub new_memory_pages_counter: Option<UInt32<E>>,
    pub new_did_call_or_ret_recently: Option<Boolean>,
    pub new_forward_queue_state: Option<Num<E>>,
    pub new_forward_queue_length: Option<UInt32<E>>,
    pub new_rollback_queue_state: Option<Num<E>>,
    pub new_rollback_queue_length: Option<UInt32<E>>,
    pub update_decommittment_queue: Option<Boolean>,
    pub new_decommittment_queue_state: Option<[Num<E>; 3]>,
    pub new_decommittment_queue_length: Option<UInt32<E>>,
    pub context_u128_new_value: Option<(Boolean, [UInt64<E>; 2])>,
    pub new_heap_upper_bound: Option<(Boolean, UInt32<E>)>,
    pub new_aux_heap_upper_bound: Option<(Boolean, UInt32<E>)>,
    // all below is for UMA largely. It's accumulated instead of passing &mut VmLocalState<E, 3> into opcode in
    // a similar manner to other possible unused updates
    pub new_memory_queue_state: Option<[Num<E>; 3]>, // UMA can take current_state.memory_queue... params and update it, as they ARE current
    pub new_memory_queue_length: Option<UInt32<E>>,
    pub pending_arithmetic_operations: Option<Vec<(PendingArithmeticRelation<E>, Boolean)>>,
}

use crate::vm::vm_state::GlobalContext;

pub trait InCircuitOpcode<E: Engine>: PartialOpcodePropsMarker {
    // fn should_use_nonspecialized_implementation(&self) -> bool;
    fn apply<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    >(
        &self, // should be just zkevm_opcode_def structure, or some specialized marker
        cs: &mut CS,
        current_state: &VmLocalState<E, 3>,
        common_opcode_state: &CommonOpcodeState<E>,
        opcode_carry_parts: &OpcodeCarryParts<E>,
        global_context: &GlobalContext<E>,
        optimizer: &mut OptimizationContext<E>,
        round_function: &R,
        witness_oracle: &mut impl WitnessOracle<E>,
    ) -> Result<OpcodePartialApplicationResult<E, Self>, SynthesisError>;
}

impl<E: Engine, M: PartialOpcodePropsMarker> Default for OpcodePartialApplicationResult<E, M> {
    fn default() -> Self {
        OpcodePartialApplicationResult::<E, M> {
            marker: <M as PartialOpcodePropsMarker>::default(),
            applies: Boolean::constant(false),
            pending_sponges: vec![],
            dst0_value: None,
            dst1_value: None,
            flags: vec![],
            specific_registers_updates: vec![],
            zero_out_specific_registers: vec![],
            remove_ptr_on_specific_registers: vec![],
            pending_exception: None,
            callstack: None,
            ergs_left: None,
            new_pc: None,
            new_ergs_per_pubdata_byte: None,
            new_tx_number_in_block: None,
            new_memory_pages_counter: None,
            new_did_call_or_ret_recently: None,
            new_forward_queue_state: None,
            new_forward_queue_length: None,
            new_rollback_queue_state: None,
            new_rollback_queue_length: None,
            update_decommittment_queue: None,
            new_decommittment_queue_state: None,
            new_decommittment_queue_length: None,
            context_u128_new_value: None,
            new_memory_queue_state: None,
            new_memory_queue_length: None,
            pending_arithmetic_operations: None,
            new_heap_upper_bound: None,
            new_aux_heap_upper_bound: None,
        }
    }
}
