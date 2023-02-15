use super::witness_oracle::WitnessOracle;
use super::*;

use crate::glue::traits::*;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;
use crate::scheduler::queues::FullSpongeLikeQueueState;
use crate::vm::vm_state::GlobalContext;
use crate::vm::vm_state::VmGlobalState;
use cs_derive::*;

#[derive(Derivative, CSAllocatable, CSWitnessable, CSVariableLengthEncodable)]
#[derivative(Clone, Debug)]
pub struct VmInputData<E: Engine> {
    pub rollback_queue_tail_for_block: Num<E>,
    pub memory_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub decommitment_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub per_block_context: GlobalContext<E>,
}

impl<E: Engine> CircuitEmpty<E> for VmInputData<E> {
    fn empty() -> Self {
        Self {
            rollback_queue_tail_for_block: Num::zero(),
            memory_queue_initial_state: FullSpongeLikeQueueState::<E>::empty(),
            decommitment_queue_initial_state: FullSpongeLikeQueueState::<E>::empty(),
            per_block_context: GlobalContext::<E>::empty(),
        }
    }
}

#[derive(
    Derivative, CSAllocatable, CSWitnessable, CSSelectable, CSEqual, CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct VmOutputData<E: Engine> {
    pub memory_queue_final_state: FullSpongeLikeQueueState<E>,
    pub decommitment_queue_final_state: FullSpongeLikeQueueState<E>,
    pub log_queue_final_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for VmOutputData<E> {
    fn empty() -> Self {
        Self {
            memory_queue_final_state: FullSpongeLikeQueueState::<E>::empty(),
            decommitment_queue_final_state: FullSpongeLikeQueueState::<E>::empty(),
            log_queue_final_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
        }
    }
}

pub type VmCircuitInputOutput<E> =
    crate::inputs::ClosedFormInput<E, VmGlobalState<E, 3>, VmInputData<E>, VmOutputData<E>>;
pub type VmCircuitInputOutputWitness<E> =
    crate::inputs::ClosedFormInputWitness<E, VmGlobalState<E, 3>, VmInputData<E>, VmOutputData<E>>;

use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug(bound = ""))]
#[serde(bound = "")]
pub struct VmCircuitWitness<E: Engine, W: WitnessOracle<E>> {
    pub closed_form_input: VmCircuitInputOutputWitness<E>,
    #[derivative(Debug = "ignore")]
    pub witness_oracle: W,
}
