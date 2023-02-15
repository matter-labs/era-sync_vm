use super::*;
use franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget;

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
pub struct Sha256RoundFunctionFSM<E: Engine> {
    pub read_precompile_call: Boolean,
    pub read_words_for_round: Boolean,
    pub completed: Boolean,
    pub sha256_inner_state: [Num<E>; 8],
    pub timestamp_to_use_for_read: UInt32<E>,
    pub timestamp_to_use_for_write: UInt32<E>,
    pub precompile_call_params: Sha256PrecompileCallParams<E>,
}

impl<E: Engine> CircuitEmpty<E> for Sha256RoundFunctionFSM<E> {
    fn empty() -> Self {
        Self {
            read_precompile_call: Boolean::constant(false),
            read_words_for_round: Boolean::constant(false),
            completed: Boolean::constant(false),
            sha256_inner_state: Sha256Gadget::iv_as_nums(),
            timestamp_to_use_for_read: UInt32::<E>::zero(),
            timestamp_to_use_for_write: UInt32::<E>::zero(),
            precompile_call_params: Sha256PrecompileCallParams::<E>::empty(),
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
pub struct Sha256RoundFunctionFSMInputOutput<E: Engine> {
    pub internal_fsm: Sha256RoundFunctionFSM<E>,
    pub log_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub memory_queue_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for Sha256RoundFunctionFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            internal_fsm: CircuitEmpty::<E>::empty(),
            log_queue_state: CircuitEmpty::<E>::empty(),
            memory_queue_state: CircuitEmpty::<E>::empty(),
        }
    }
}

use crate::precompiles::*;

pub type Sha256RoundFunctionCircuitInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    Sha256RoundFunctionFSMInputOutput<E>,
    PrecompileFunctionInputData<E>,
    PrecompileFunctionOutputData<E>,
>;
pub type Sha256RoundFunctionCircuitInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    Sha256RoundFunctionFSMInputOutput<E>,
    PrecompileFunctionInputData<E>,
    PrecompileFunctionOutputData<E>,
>;

use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct Sha256RoundFunctionCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: Sha256RoundFunctionCircuitInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<StorageLogRecord<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub requests_queue_witness: FixedWidthEncodingGenericQueueWitness<E, StorageLogRecord<E>, 5>,
    pub memory_reads_witness: Vec<Vec<BigUint>>,
}
