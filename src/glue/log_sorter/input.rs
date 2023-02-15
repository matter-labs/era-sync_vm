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
pub struct EventsDeduplicatorFSMInputOutput<E: Engine> {
    pub lhs_accumulator: Num<E>,
    pub rhs_accumulator: Num<E>,
    pub initial_unsorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub intermediate_sorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub final_result_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub previous_packed_key: Num<E>,
    pub previous_item: StorageLogRecord<E>,
}

impl<E: Engine> CircuitEmpty<E> for EventsDeduplicatorFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            lhs_accumulator: CircuitEmpty::<E>::empty(),
            rhs_accumulator: CircuitEmpty::<E>::empty(),
            initial_unsorted_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            intermediate_sorted_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            final_result_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            previous_packed_key: Num::zero(),
            previous_item: StorageLogRecord::<E>::empty(),
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
pub struct EventsDeduplicatorInputData<E: Engine> {
    pub initial_log_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub intermediate_sorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for EventsDeduplicatorInputData<E> {
    fn empty() -> Self {
        Self {
            initial_log_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            intermediate_sorted_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
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
pub struct EventsDeduplicatorOutputData<E: Engine> {
    pub final_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for EventsDeduplicatorOutputData<E> {
    fn empty() -> Self {
        Self {
            final_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
        }
    }
}

pub type EventsDeduplicatorInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    EventsDeduplicatorFSMInputOutput<E>,
    EventsDeduplicatorInputData<E>,
    EventsDeduplicatorOutputData<E>,
>;
pub type EventsDeduplicatorInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    EventsDeduplicatorFSMInputOutput<E>,
    EventsDeduplicatorInputData<E>,
    EventsDeduplicatorOutputData<E>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct EventsDeduplicatorInstanceWitness<E: Engine> {
    pub closed_form_input: EventsDeduplicatorInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub initial_queue_witness: FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,

    #[serde(bound(
        serialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub intermediate_sorted_queue_witness:
        FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,
}
