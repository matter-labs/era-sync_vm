use std::iter::empty;

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
pub struct MessagesMerklizerInputData<E: Engine> {
    pub input_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for MessagesMerklizerInputData<E> {
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
pub struct MessagesMerklizerOutputData<E: Engine> {
    pub linear_hash: Bytes32<E>, // has better encoding automatically
    pub root_hash: Bytes32<E>,   // has better encoding automatically
}

impl<E: Engine> CircuitEmpty<E> for MessagesMerklizerOutputData<E> {
    fn empty() -> Self {
        Self {
            linear_hash: Bytes32::<E>::empty(),
            root_hash: Bytes32::<E>::empty(),
        }
    }
}

pub type MessagesMerklizerInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    (),
    MessagesMerklizerInputData<E>,
    MessagesMerklizerOutputData<E>,
>;
pub type MessagesMerklizerInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    (),
    MessagesMerklizerInputData<E>,
    MessagesMerklizerOutputData<E>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct MessagesMerklizerInstanceWitness<
    E: Engine,
    const N: usize,
    const SERIALIZATION_WIDTH: usize,
    I: CircuitFixedLengthEncodableExt<E, N>
        + CircuitFixedLengthDecodableExt<E, N>
        + ByteSerializable<E, SERIALIZATION_WIDTH>,
> {
    pub closed_form_input: MessagesMerklizerInputOutputWitness<E>,
    #[serde(bound(
        serialize = "[E::Fr; N]: serde::Serialize, <I as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "[E::Fr; N]: serde::de::DeserializeOwned, <I as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub input_queue_witness: FixedWidthEncodingGenericQueueWitness<E, I, N>,
}

pub const MESSAGE_SERIALIZATION_BYTES: usize = 1 + 1 + 2 + 20 + 32 + 32;

// we only do it for a limited purpose here, as it will only be for logs
impl<E: Engine> ByteSerializable<E, MESSAGE_SERIALIZATION_BYTES> for StorageLogRecord<E> {
    fn serialize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Byte<E>; MESSAGE_SERIALIZATION_BYTES], SynthesisError> {
        let mut result = [Byte::zero(); MESSAGE_SERIALIZATION_BYTES];
        let mut offset = 0;
        result[0] = self.shard_id;
        offset += 1;

        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&self.is_service, E::Fr::one());
        let value = lc.into_num(cs)?;
        let byte = Byte::from_num_unconstrained(cs, value);
        let bytes_be = vec![byte];
        assert_eq!(bytes_be.len(), 1);
        result[offset..(offset + bytes_be.len())].copy_from_slice(&bytes_be);
        offset += bytes_be.len();

        let bytes_be = self.tx_number_in_block.into_be_bytes(cs)?;
        assert_eq!(bytes_be.len(), 2);
        result[offset..(offset + bytes_be.len())].copy_from_slice(&bytes_be);
        offset += bytes_be.len();

        let bytes_be = self.address.into_be_bytes(cs)?;
        assert_eq!(bytes_be.len(), 20);
        result[offset..(offset + bytes_be.len())].copy_from_slice(&bytes_be);
        offset += bytes_be.len();

        let bytes_be = self.key.into_be_bytes(cs)?;
        assert_eq!(bytes_be.len(), 32);
        result[offset..(offset + bytes_be.len())].copy_from_slice(&bytes_be);
        offset += bytes_be.len();

        let bytes_be = self.written_value.into_be_bytes(cs)?;
        assert_eq!(bytes_be.len(), 32);
        result[offset..(offset + bytes_be.len())].copy_from_slice(&bytes_be);
        offset += bytes_be.len();

        assert_eq!(offset, MESSAGE_SERIALIZATION_BYTES);

        Ok(result)
    }
}
