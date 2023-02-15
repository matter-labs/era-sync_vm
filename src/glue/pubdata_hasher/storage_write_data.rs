use super::*;

use cs_derive::*;
use derivative::*;

pub const INITIAL_STORAGE_WRITE_ENCODING_LENGTH: usize = 3;
pub const REPEATED_STORAGE_WRITE_ENCODING_LENGTH: usize = 2;

#[derive(
    Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, FixedLengthEncodableExt,
)]
#[EncodingLength = "INITIAL_STORAGE_WRITE_ENCODING_LENGTH"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct InitialStorageWriteData<E: Engine> {
    pub key: [Byte<E>; 32],
    pub value: [Byte<E>; 32],
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, INITIAL_STORAGE_WRITE_ENCODING_LENGTH>
    for InitialStorageWriteData<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> InitialStorageWriteData<E> {
    pub fn empty() -> Self {
        InitialStorageWriteData {
            key: [Byte::zero(); 32],
            value: [Byte::zero(); 32],
        }
    }

    pub fn new(key: [Byte<E>; 32], value: [Byte<E>; 32]) -> Self {
        Self { key, value }
    }

    pub fn pack<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; INITIAL_STORAGE_WRITE_ENCODING_LENGTH], SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // we pack the structure as follows:
        // 30 bytes, then 30 bytes, then the rest

        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        for el in self.key[..30].iter() {
            lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
            shift += 8;
        }
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        for el in self.key[30..].iter().chain(self.value[..28].iter()) {
            lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
            shift += 8;
        }
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el1 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        for el in self.value[28..].iter() {
            lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
            shift += 8;
        }
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el2 = lc.into_num(cs)?;

        Ok([el0, el1, el2])
    }
}

#[derive(
    Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, FixedLengthEncodableExt,
)]
#[EncodingLength = "REPEATED_STORAGE_WRITE_ENCODING_LENGTH"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct RepeatedStorageWriteData<E: Engine> {
    pub index: UInt64<E>,
    pub value: [Byte<E>; 32],
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, REPEATED_STORAGE_WRITE_ENCODING_LENGTH>
    for RepeatedStorageWriteData<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> RepeatedStorageWriteData<E> {
    pub fn empty() -> Self {
        RepeatedStorageWriteData {
            index: UInt64::zero(),
            value: [Byte::zero(); 32],
        }
    }

    pub fn new(index: UInt64<E>, value: [Byte<E>; 32]) -> Self {
        Self { index, value }
    }

    pub fn pack<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; REPEATED_STORAGE_WRITE_ENCODING_LENGTH], SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // we pack the structure as follows:
        // 8+16 bytes, then 16 bytes, then the rest

        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        let mut shift = 0;

        lc.add_assign_number_with_coeff(&self.index.inner, shifts[0]);
        shift += 64;

        for el in self.value[..16].iter() {
            lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
            shift += 8;
        }
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        for el in self.value[16..].iter() {
            lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
            shift += 8;
        }
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el1 = lc.into_num(cs)?;

        Ok([el0, el1])
    }
}

pub trait ByteSerializable<E: Engine, const N: usize>: Clone {
    fn serialize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Byte<E>; N], SynthesisError>;
}

use crate::glue::optimizable_queue::FixedWidthEncodingGenericQueue;

pub type InitialStorageWriteDataQueue<E> = FixedWidthEncodingGenericQueue<
    E,
    InitialStorageWriteData<E>,
    INITIAL_STORAGE_WRITE_ENCODING_LENGTH,
>;
pub type RepeatedStorageWriteDataQueue<E> = FixedWidthEncodingGenericQueue<
    E,
    RepeatedStorageWriteData<E>,
    REPEATED_STORAGE_WRITE_ENCODING_LENGTH,
>;

use crate::scheduler::queues::{StorageLogRecord, STORAGE_LOG_RECORD_ENCODING_LEN};

pub type L1MessagesDataQueue<E> =
    FixedWidthEncodingGenericQueue<E, StorageLogRecord<E>, STORAGE_LOG_RECORD_ENCODING_LEN>;

impl<E: Engine> ByteSerializable<E, 40> for RepeatedStorageWriteData<E> {
    fn serialize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Byte<E>; 40], SynthesisError> {
        let mut result = [Byte::zero(); 40];

        let key = self.index.into_be_bytes(cs)?;
        assert!(key.len() == 8);
        result[0..8].copy_from_slice(&key);
        result[8..40].copy_from_slice(&self.value);

        Ok(result)
    }
}

impl<E: Engine> ByteSerializable<E, 64> for InitialStorageWriteData<E> {
    fn serialize<CS: ConstraintSystem<E>>(
        &self,
        _cs: &mut CS,
    ) -> Result<[Byte<E>; 64], SynthesisError> {
        let mut result = [Byte::zero(); 64];

        result[0..32].copy_from_slice(&self.key);
        result[32..64].copy_from_slice(&self.value);

        Ok(result)
    }
}
