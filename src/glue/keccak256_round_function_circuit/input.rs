use super::*;
use cs_derive::*;

use crate::precompiles::*;
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
pub struct Keccak256RoundFunctionFSM<E: Engine> {
    pub precompile_state: KeccakPrecompileState<E>,
    pub log_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub memory_queue_state: FullSpongeLikeQueueState<E>,
}

pub type Keccak256RoundFunctionInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    Keccak256RoundFunctionFSM<E>,
    PrecompileFunctionInputData<E>,
    PrecompileFunctionOutputData<E>,
>;
pub type Keccak256RoundFunctionInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    Keccak256RoundFunctionFSM<E>,
    PrecompileFunctionInputData<E>,
    PrecompileFunctionOutputData<E>,
>;

use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct Keccak256RoundFunctionInstanceWitness<E: Engine> {
    pub closed_form_input: Keccak256RoundFunctionInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub requests_queue_witness: FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,
    pub memory_reads_witness: Vec<Vec<BigUint>>,
}
