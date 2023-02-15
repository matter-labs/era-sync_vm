use super::ports::ArithmeticFlagsPort;
use super::*;
use crate::vm::vm_cycle::pre_state::*;

pub mod callstack;
pub mod execution_context;
pub mod saved_contract_context;
use zkevm_opcode_defs::system_params::NUM_SPONGES;
use zkevm_opcode_defs::MAX_PENDING_CYCLES;

use crate::scheduler::queues::decommit_query::*;

use self::callstack::Callstack;
use self::saved_contract_context::*;
use crate::vm::primitives::register_view::*;
use cs_derive::*;
use derivative::*;

use crate::glue::traits::*;

// this is a state that is local in a sense that it contains all the state
// of the VM without external oracles such as RAM or storage
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct VmLocalState<E: Engine, const SW: usize> {
    pub previous_code_word: [UInt64<E>; 4],
    pub registers: [Register<E>; zkevm_opcode_defs::REGISTERS_COUNT],
    pub flags: ArithmeticFlagsPort<E>,
    pub timestamp: UInt32<E>,
    pub memory_page_counter: UInt32<E>,
    pub tx_number_in_block: UInt16<E>,
    pub previous_super_pc: UInt16<E>,
    pub pending_exception: Boolean,
    pub did_call_or_ret_recently: Boolean,
    pub ergs_per_pubdata_byte: UInt32<E>,
    pub callstack: Callstack<E, SW>,
    pub pending_sponges: PendingRoundFunctions<E, SW>,
    pub memory_queue_state: [Num<E>; SW],
    pub memory_queue_length: UInt32<E>,
    pub code_decommittment_queue_state: [Num<E>; SW],
    pub code_decommittment_queue_length: UInt32<E>,
    pub context_composite_u128: [UInt64<E>; 2],
    pub pending_arithmetic_operations: Vec<(PendingArithmeticRelation<E>, Boolean)>,
}

impl<E: Engine, const SW: usize> VmLocalState<E, SW> {
    pub fn split(
        self,
    ) -> (
        VmGlobalState<E, SW>,
        PendingRoundFunctions<E, SW>,
        Vec<(PendingArithmeticRelation<E>, Boolean)>,
    ) {
        let VmLocalState::<E, SW> {
            registers,
            flags,
            timestamp,
            memory_page_counter,
            tx_number_in_block,
            ergs_per_pubdata_byte,
            callstack,
            memory_queue_state,
            memory_queue_length,
            code_decommittment_queue_state,
            code_decommittment_queue_length,
            previous_code_word,
            previous_super_pc,
            pending_exception,
            did_call_or_ret_recently,
            pending_sponges,
            pending_arithmetic_operations,
            context_composite_u128,
            ..
        } = self;

        let global_state = VmGlobalState::<E, SW> {
            registers,
            flags,
            timestamp,
            memory_page_counter,
            tx_number_in_block,
            ergs_per_pubdata_byte,
            callstack,
            memory_queue_state,
            memory_queue_length,
            code_decommittment_queue_state,
            code_decommittment_queue_length,
            previous_code_word,
            previous_super_pc,
            did_call_or_ret_recently,
            pending_exception,
            context_composite_u128,
        };
        (global_state, pending_sponges, pending_arithmetic_operations)
    }
}

// this is a state that will be saved and passed between different VM isntanced
#[derive(
    Derivative, CSAllocatable, CSEqual, CSSelectable, CSWitnessable, CSVariableLengthEncodable,
)]
#[derivative(Clone, Copy, Debug)]
pub struct VmGlobalState<E: Engine, const SW: usize> {
    pub registers: [Register<E>; zkevm_opcode_defs::REGISTERS_COUNT],
    pub flags: ArithmeticFlagsPort<E>,
    pub timestamp: UInt32<E>,
    pub memory_page_counter: UInt32<E>,
    pub tx_number_in_block: UInt16<E>,
    pub ergs_per_pubdata_byte: UInt32<E>,
    pub callstack: Callstack<E, SW>,
    pub memory_queue_state: [Num<E>; SW],
    pub memory_queue_length: UInt32<E>,
    pub code_decommittment_queue_state: [Num<E>; SW],
    pub code_decommittment_queue_length: UInt32<E>,
    pub context_composite_u128: [UInt64<E>; 2],
    pub previous_code_word: [UInt64<E>; 4],
    pub previous_super_pc: UInt16<E>,
    pub did_call_or_ret_recently: Boolean,
    pub pending_exception: Boolean,
}

impl<E: Engine, const SW: usize> CircuitEmpty<E> for VmGlobalState<E, SW> {
    fn empty() -> Self {
        Self {
            registers: [Register::<E>::empty(); zkevm_opcode_defs::REGISTERS_COUNT],
            flags: ArithmeticFlagsPort::empty(),
            timestamp: UInt32::zero(),
            memory_page_counter: UInt32::zero(),
            tx_number_in_block: UInt16::zero(),
            ergs_per_pubdata_byte: UInt32::zero(),
            callstack: Callstack::<E, SW>::empty(),
            memory_queue_state: [Num::zero(); SW],
            memory_queue_length: UInt32::zero(),
            code_decommittment_queue_state: [Num::zero(); SW],
            code_decommittment_queue_length: UInt32::zero(),
            context_composite_u128: [UInt64::zero(); 2],
            previous_code_word: [UInt64::zero(); 4],
            previous_super_pc: UInt16::zero(),
            did_call_or_ret_recently: Boolean::constant(false),
            pending_exception: Boolean::constant(false),
        }
    }
}

impl<E: Engine, const SW: usize> Into<VmLocalState<E, SW>> for VmGlobalState<E, SW> {
    fn into(self) -> VmLocalState<E, SW> {
        let VmGlobalState::<E, SW> {
            registers,
            flags,
            timestamp,
            memory_page_counter,
            tx_number_in_block,
            ergs_per_pubdata_byte,
            callstack,
            memory_queue_state,
            memory_queue_length,
            code_decommittment_queue_state,
            code_decommittment_queue_length,
            previous_code_word,
            previous_super_pc,
            did_call_or_ret_recently,
            context_composite_u128,
            pending_exception,
        } = self;

        VmLocalState {
            registers,
            flags,
            timestamp,
            memory_page_counter,
            tx_number_in_block,
            ergs_per_pubdata_byte,
            callstack,
            memory_queue_state,
            memory_queue_length,
            code_decommittment_queue_state,
            code_decommittment_queue_length,
            previous_code_word,
            previous_super_pc,
            did_call_or_ret_recently,
            pending_exception,
            context_composite_u128,
            pending_sponges: PendingRoundFunctions::<E, SW>::empty(),
            pending_arithmetic_operations: vec![],
        }
    }
}

#[derive(Derivative, CSAllocatable, CSWitnessable, CSVariableLengthEncodable)]
#[derivative(Clone, Copy, Debug)]
pub struct GlobalContext<E: Engine> {
    pub zkporter_is_available: Boolean,
    pub default_aa_code_hash: UInt256<E>,
}

impl<E: Engine> GlobalContext<E> {
    pub fn empty() -> Self {
        Self {
            zkporter_is_available: Boolean::constant(false),
            default_aa_code_hash: UInt256::<E>::zero(),
        }
    }
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSSelectable,
    CSEqual,
    CSOrdering,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct PendingRecord<E: Engine, const SWIDTH: usize> {
    pub initial_state: [Num<E>; SWIDTH],
    pub final_state: [Num<E>; SWIDTH],
    pub is_used: Boolean,
}

impl<E: Engine, const SWIDTH: usize> Copy for PendingRecord<E, SWIDTH> {}

impl<E: Engine, const SWIDTH: usize> PendingRecord<E, SWIDTH> {
    pub fn empty() -> Self {
        Self {
            initial_state: [Num::<E>::zero(); SWIDTH],
            final_state: [Num::<E>::zero(); SWIDTH],
            is_used: Boolean::constant(false),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSWitnessable, CSVariableLengthEncodable)]
#[derivative(Clone, Debug)]
pub struct PendingRoundFunctions<E: Engine, const SWIDTH: usize> {
    pub records: [[PendingRecord<E, SWIDTH>; NUM_SPONGES]; MAX_PENDING_CYCLES],
}

impl<E: Engine, const SWIDTH: usize> PendingRoundFunctions<E, SWIDTH> {
    pub fn empty() -> Self {
        Self {
            records: [[PendingRecord::empty(); NUM_SPONGES]; MAX_PENDING_CYCLES],
        }
    }

    pub fn is_any_pending<CS>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut candidates = vec![];
        for cycle in self.records.iter() {
            for record in cycle.iter() {
                candidates.push(record.is_used);
            }
        }

        smart_or(cs, &candidates)
    }
}

impl<E: Engine, const SWIDTH: usize> Copy for PendingRoundFunctions<E, SWIDTH> {}

// #[derive(Derivative)]
// #[derivative(Clone, Debug)]
// pub struct VmWitnessState<E: Engine, const SW: usize> {
//     pub context_stack_witness: ContextStack<E, SW>,
// }

// impl<E: Engine, const SWIDTH: usize> VmWitnessState<E, SWIDTH> {
//     pub fn get_next_memory_read(&mut self) -> Option<BigUint> {
//         todo!()
//     }
// }
