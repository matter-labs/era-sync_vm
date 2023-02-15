use super::*;
use cs_derive::*;

use crate::glue::pubdata_hasher::storage_write_data::ByteSerializable;
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
pub struct PubdataHasherInputData<E: Engine> {
    pub input_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for PubdataHasherInputData<E> {
    fn empty() -> Self {
        Self {
            input_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
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
pub struct PubdataHasherOutputData<E: Engine> {
    pub pubdata_hash: Bytes32<E>, // has better encoding automatically
}

impl<E: Engine> CircuitEmpty<E> for PubdataHasherOutputData<E> {
    fn empty() -> Self {
        Self {
            pubdata_hash: Bytes32::<E>::empty(),
        }
    }
}

pub type PubdataHasherInputOutput<E> =
    crate::inputs::ClosedFormInput<E, (), PubdataHasherInputData<E>, PubdataHasherOutputData<E>>;
pub type PubdataHasherInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    (),
    PubdataHasherInputData<E>,
    PubdataHasherOutputData<E>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct PubdataHasherInstanceWitness<
    E: Engine,
    const N: usize,
    const SERIALIZATION_WIDTH: usize,
    I: CircuitFixedLengthEncodableExt<E, N>
        + CircuitFixedLengthDecodableExt<E, N>
        + ByteSerializable<E, SERIALIZATION_WIDTH>,
> {
    pub closed_form_input: PubdataHasherInputOutputWitness<E>,
    #[serde(bound(
        serialize = "[E::Fr; N]: serde::Serialize, <I as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "[E::Fr; N]: serde::de::DeserializeOwned, <I as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub input_queue_witness: FixedWidthEncodingGenericQueueWitness<E, I, N>,
}
