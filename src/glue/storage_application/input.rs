use super::*;
use cs_derive::*;

use crate::glue::optimizable_queue::FixedWidthEncodingGenericQueue;
use crate::inputs::*;
use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct StorageApplicationFSM<E: Engine> {
    pub root_hash: [UInt128<E>; 2],
    pub shard: UInt8<E>,
    pub next_enumeration_counter: UInt64<E>,
    pub current_storage_application_log_state: FixedWidthEncodingGenericQueueState<E>,
    pub repeated_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub initial_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for StorageApplicationFSM<E> {
    fn empty() -> Self {
        Self {
            root_hash: [UInt128::<E>::zero(); 2],
            shard: UInt8::<E>::zero(),
            next_enumeration_counter: UInt64::<E>::zero(),
            current_storage_application_log_state: FixedWidthEncodingGenericQueueState::empty(),
            repeated_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState::empty(),
            initial_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState::empty(),
        }
    }
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct StorageApplicationInputData<E: Engine> {
    pub initial_next_enumeration_counter: UInt64<E>,
    pub shard: UInt8<E>,
    pub initial_root: [UInt128<E>; 2],
    pub storage_application_log_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for StorageApplicationInputData<E> {
    fn empty() -> Self {
        Self {
            initial_next_enumeration_counter: UInt64::<E>::zero(),
            shard: UInt8::<E>::zero(),
            initial_root: <[UInt128<E>; 2]>::default(),
            storage_application_log_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
        }
    }
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct StorageApplicationOutputData<E: Engine> {
    pub final_next_enumeration_counter: UInt64<E>,
    pub final_root: [UInt128<E>; 2],
    pub repeated_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub initial_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for StorageApplicationOutputData<E> {
    fn empty() -> Self {
        Self {
            final_next_enumeration_counter: UInt64::<E>::zero(),
            final_root: <[UInt128<E>; 2]>::default(),
            repeated_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            initial_writes_pubdata_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
        }
    }
}

pub type StorageApplicationCycleInputOutput<E> = ClosedFormInput<
    E,
    StorageApplicationFSM<E>,
    StorageApplicationInputData<E>,
    StorageApplicationOutputData<E>,
>;
pub type StorageApplicationCycleInputOutputWitness<E> = ClosedFormInputWitness<
    E,
    StorageApplicationFSM<E>,
    StorageApplicationInputData<E>,
    StorageApplicationOutputData<E>,
>;

pub const STORAGE_DEPTH: usize = 256;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct StorageApplicationCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: StorageApplicationCycleInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub storage_queue_witness: FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,
    #[derivative(Debug = "ignore")]
    pub merkle_paths: Vec<Vec<[u32; 8]>>,
    pub leaf_indexes_for_reads: Vec<u64>,
}
