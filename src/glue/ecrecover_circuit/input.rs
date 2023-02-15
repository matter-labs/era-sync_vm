use super::*;

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
pub struct EcrecoverCircuitFSMInputOutput<E: Engine> {
    pub log_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub memory_queue_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for EcrecoverCircuitFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            log_queue_state: CircuitEmpty::<E>::empty(),
            memory_queue_state: CircuitEmpty::<E>::empty(),
        }
    }
}

use crate::precompiles::*;

pub type EcrecoverCircuitInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    EcrecoverCircuitFSMInputOutput<E>,
    PrecompileFunctionInputData<E>,
    PrecompileFunctionOutputData<E>,
>;
pub type EcrecoverCircuitInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    EcrecoverCircuitFSMInputOutput<E>,
    PrecompileFunctionInputData<E>,
    PrecompileFunctionOutputData<E>,
>;

use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct EcrecoverCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: EcrecoverCircuitInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub requests_queue_witness: FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,
    pub memory_reads_witness: Vec<Vec<BigUint>>,
}
