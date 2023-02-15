use super::*;
use cs_derive::*;

use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;

// FSM

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
pub struct StorageDeduplicatorFSMInputOutput<E: Engine> {
    pub lhs_accumulator: Num<E>,
    pub rhs_accumulator: Num<E>,
    pub current_unsorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub current_intermediate_sorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub current_final_sorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub cycle_idx: UInt32<E>,
    pub previous_packed_key: [Num<E>; 2],
    pub previous_key: UInt256<E>,
    pub previous_address: UInt160<E>,
    pub previous_timestamp: UInt32<E>,
    pub previous_shard_id: Byte<E>,
    pub this_cell_has_explicit_read_and_rollback_depth_zero: Boolean,
    pub this_cell_base_value: UInt256<E>,
    pub this_cell_current_value: UInt256<E>,
    pub this_cell_current_depth: UInt32<E>,
}

impl<E: Engine> CircuitEmpty<E> for StorageDeduplicatorFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            lhs_accumulator: CircuitEmpty::<E>::empty(),
            rhs_accumulator: CircuitEmpty::<E>::empty(),
            current_unsorted_queue_state: CircuitEmpty::<E>::empty(),
            current_intermediate_sorted_queue_state: CircuitEmpty::<E>::empty(),
            current_final_sorted_queue_state: CircuitEmpty::<E>::empty(),
            cycle_idx: CircuitEmpty::<E>::empty(),
            previous_packed_key: [Num::zero(); 2],
            previous_key: UInt256::<E>::zero(),
            previous_address: CircuitEmpty::<E>::empty(),
            previous_timestamp: CircuitEmpty::<E>::empty(),
            previous_shard_id: Byte::zero(),
            this_cell_has_explicit_read_and_rollback_depth_zero: CircuitEmpty::<E>::empty(),
            this_cell_base_value: UInt256::<E>::zero(),
            this_cell_current_value: UInt256::<E>::zero(),
            this_cell_current_depth: CircuitEmpty::<E>::empty(),
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
pub struct StorageDeduplicatorInputData<E: Engine> {
    pub unsorted_log_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub intermediate_sorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for StorageDeduplicatorInputData<E> {
    fn empty() -> Self {
        Self {
            unsorted_log_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
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
pub struct StorageDeduplicatorOutputData<E: Engine> {
    pub final_sorted_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for StorageDeduplicatorOutputData<E> {
    fn empty() -> Self {
        Self {
            final_sorted_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
        }
    }
}

pub type StorageDeduplicatorInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    StorageDeduplicatorFSMInputOutput<E>,
    StorageDeduplicatorInputData<E>,
    StorageDeduplicatorOutputData<E>,
>;
pub type StorageDeduplicatorInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    StorageDeduplicatorFSMInputOutput<E>,
    StorageDeduplicatorInputData<E>,
    StorageDeduplicatorOutputData<E>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct StorageDeduplicatorInstanceWitness<E: Engine> {
    pub closed_form_input: StorageDeduplicatorInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub unsorted_queue_witness: FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,

    #[serde(bound(
        serialize = "<TimestampedStorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<TimestampedStorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub intermediate_sorted_queue_witness:
        FixedWidthEncodingGenericQueueWitness<E, TimestampedStorageLogRecord<E>, 5>,
}
