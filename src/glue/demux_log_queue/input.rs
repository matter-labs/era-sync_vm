use super::*;
use cs_derive::*;

use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;

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
pub struct LogDemuxerFSMInputOutput<E: Engine> {
    pub initial_log_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub storage_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub events_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub l1messages_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub keccak256_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub sha256_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub ecrecover_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for LogDemuxerFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            initial_log_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            storage_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            events_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            l1messages_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            keccak256_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            sha256_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            ecrecover_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
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
pub struct LogDemuxerInputData<E: Engine> {
    pub initial_log_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for LogDemuxerInputData<E> {
    fn empty() -> Self {
        Self {
            initial_log_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
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
pub struct LogDemuxerOutputData<E: Engine> {
    pub storage_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub events_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub l1messages_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub keccak256_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub sha256_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub ecrecover_access_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for LogDemuxerOutputData<E> {
    fn empty() -> Self {
        Self {
            storage_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            events_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            l1messages_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            keccak256_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            sha256_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            ecrecover_access_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
        }
    }
}

pub type LogDemuxerInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    LogDemuxerFSMInputOutput<E>,
    LogDemuxerInputData<E>,
    LogDemuxerOutputData<E>,
>;

pub type LogDemuxerInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    LogDemuxerFSMInputOutput<E>,
    LogDemuxerInputData<E>,
    LogDemuxerOutputData<E>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct LogDemuxerCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: LogDemuxerInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub initial_queue_witness: FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,
}
