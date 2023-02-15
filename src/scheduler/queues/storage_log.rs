use super::*;
use crate::vm::primitives::small_uints::*;
use cs_derive::*;
use num_traits::Zero;
use std::convert::TryInto;

pub const STORAGE_LOG_RECORD_ENCODING_LEN: usize = 5;

#[derive(Derivative, CSWitnessable, CSAllocatable, CSSelectable, CSEqual)]
#[derivative(Clone, Debug)]
pub struct StorageLogRecord<E: Engine> {
    pub address: UInt160<E>,
    pub key: UInt256<E>,
    pub read_value: UInt256<E>,
    pub written_value: UInt256<E>,
    pub r_w_flag: Boolean,
    pub aux_byte: Byte<E>,
    pub rollback: Boolean,
    pub is_service: Boolean,
    pub shard_id: Byte<E>,
    pub tx_number_in_block: UInt16<E>,
    pub timestamp: UInt32<E>,
}

impl<E: Engine> CircuitVariableLengthEncodable<E> for StorageLogRecord<E> {
    fn encoding_length() -> usize {
        STORAGE_LOG_RECORD_ENCODING_LEN
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let as_array =
            <Self as CircuitFixedLengthEncodable<E, STORAGE_LOG_RECORD_ENCODING_LEN>>::encode(
                self, cs,
            )?;

        Ok(as_array.to_vec())
    }
}
pub struct LogRecordPackExtended<E: Engine> {
    pub direct: [Num<E>; STORAGE_LOG_RECORD_ENCODING_LEN],
    pub revert: [Num<E>; STORAGE_LOG_RECORD_ENCODING_LEN],
}

impl<E: Engine> StorageLogRecord<E> {
    pub fn empty() -> Self {
        Self {
            address: UInt160::<E>::zero(),
            key: UInt256::zero(),
            read_value: UInt256::zero(),
            written_value: UInt256::zero(),
            r_w_flag: Boolean::constant(false),
            aux_byte: Byte::zero(),
            rollback: Boolean::constant(false),
            is_service: Boolean::constant(false),
            shard_id: Byte::empty(),
            tx_number_in_block: UInt16::zero(),
            timestamp: UInt32::zero(),
        }
    }

    pub const CIRCUIT_ENCODING_LEN: usize = STORAGE_LOG_RECORD_ENCODING_LEN;

    pub fn pack_impl<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        with_revert: bool,
    ) -> Result<([Num<E>; STORAGE_LOG_RECORD_ENCODING_LEN], E::Fr), SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.address.inner, shifts[shift]);
        shift += 160;
        lc.add_assign_number_with_coeff(&self.key.inner[0].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.shard_id.inner, shifts[shift]);
        shift += 8;
        lc.add_assign_number_with_coeff(&self.aux_byte.inner, shifts[shift]);
        shift += 8;
        lc.add_assign_boolean_with_coeff(&self.r_w_flag, shifts[shift]);
        shift += 1;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.key.inner[1].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.key.inner[2].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.key.inner[3].inner, shifts[shift]);
        shift += 64;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        use crate::glue::storage_validity_by_grand_product::EXTENDED_TIMESTAMP_ENCODING_OFFSET;
        assert_eq!(shift, EXTENDED_TIMESTAMP_ENCODING_OFFSET);
        let el1 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.read_value.inner[0].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.read_value.inner[1].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.read_value.inner[2].inner, shifts[shift]);
        shift += 64;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el2 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.written_value.inner[0].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.written_value.inner[1].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.written_value.inner[2].inner, shifts[shift]);
        shift += 64;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el3 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.read_value.inner[3].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.written_value.inner[3].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.tx_number_in_block.inner, shifts[shift]);
        shift += 16;
        lc.add_assign_number_with_coeff(&self.timestamp.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_boolean_with_coeff(&self.is_service, shifts[shift]);
        shift += 1;
        if with_revert {
            lc.add_assign_boolean_with_coeff(&self.rollback, shifts[shift]);
        }
        let revert_flag_offset = shifts[shift];
        shift += 1;

        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);

        let el4 = lc.into_num(cs)?;

        Ok(([el0, el1, el2, el3, el4], revert_flag_offset))
    }

    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; STORAGE_LOG_RECORD_ENCODING_LEN], SynthesisError> {
        let (packed, _shift) = self.pack_impl(cs, true)?;
        Ok(packed)
    }

    pub fn pack_extended<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<LogRecordPackExtended<E>, SynthesisError> {
        let (direct, shift) = self.pack_impl(cs, false)?;
        let mut revert = direct.clone();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&revert[STORAGE_LOG_RECORD_ENCODING_LEN - 1], E::Fr::one());
        lc.add_assign_boolean_with_coeff(&Boolean::constant(true), shift);
        revert[STORAGE_LOG_RECORD_ENCODING_LEN - 1] = lc.into_num(cs)?;

        let extended_packed_log = LogRecordPackExtended { direct, revert };

        Ok(extended_packed_log)
    }
}

impl<E: Engine> StorageLogRecordWitness<E> {
    pub fn empty() -> Self {
        Self {
            address: u160::default(),
            key: BigUint::from(0u64),
            read_value: BigUint::from(0u64),
            written_value: BigUint::from(0u64),
            r_w_flag: false,
            aux_byte: 0,
            is_service: false,
            rollback: false,
            shard_id: 0u8,
            tx_number_in_block: 0,
            timestamp: 0u32,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, STORAGE_LOG_RECORD_ENCODING_LEN>
    for StorageLogRecord<E>
{
    fn encode<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; STORAGE_LOG_RECORD_ENCODING_LEN], SynthesisError> {
        let packed = self.pack(cs)?;
        Ok(packed)
    }

    fn encoding_witness(&self) -> Option<[E::Fr; STORAGE_LOG_RECORD_ENCODING_LEN]> {
        unreachable!("not used in practice")
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, STORAGE_LOG_RECORD_ENCODING_LEN>
    for StorageLogRecord<E>
{
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, STORAGE_LOG_RECORD_ENCODING_LEN>
    for StorageLogRecord<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct SortedStorageLogItem<E: Engine> {
    pub address: UInt160<E>,
    pub key: UInt256<E>,
    pub value: UInt256<E>,
    pub r_w_flag: Boolean,
    pub shard_id: Byte<E>,
}

pub(crate) const SORTED_STORAGE_LOG_RECORD_ENCODING_LEN: usize = 4;

pub const SORTED_STORAGE_LOG_KEY_DERIVATION_BYTES: usize = 20 + 32;

impl<E: Engine> SortedStorageLogItem<E> {
    pub fn empty() -> Self {
        Self {
            address: UInt160::zero(),
            key: UInt256::zero(),
            value: UInt256::zero(),
            r_w_flag: Boolean::constant(false),
            shard_id: Byte::empty(),
        }
    }

    pub const CIRCUIT_ENCODING_LEN: usize = SORTED_STORAGE_LOG_RECORD_ENCODING_LEN;

    pub fn get_key_derivation_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Byte<E>; SORTED_STORAGE_LOG_KEY_DERIVATION_BYTES], SynthesisError> {
        let address_bytes = self.address.into_be_bytes(cs)?;
        assert_eq!(address_bytes.len(), 20);
        let key_bytes = self.key.into_be_bytes(cs)?;
        assert_eq!(key_bytes.len(), 32);

        let mut result = vec![];
        result.extend(address_bytes);
        result.extend(key_bytes);

        Ok(result.try_into().unwrap())
    }
}

impl<E: Engine> CSPackable<E, SORTED_STORAGE_LOG_RECORD_ENCODING_LEN> for SortedStorageLogItem<E> {
    fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; SORTED_STORAGE_LOG_RECORD_ENCODING_LEN], SynthesisError> {
        // el0 = actor | key[0] | r_w_flag = 225
        // el1 = target | key[1] | shard_id = 232
        // el3 = key[2] | key[3] | value[0] = 192
        // el4 = value[1] | value[2] | value[3] = 192

        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.address.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.key.inner[0].inner, shifts[160]);
        lc.add_assign_boolean_with_coeff(&self.r_w_flag, shifts[160 + 64]);

        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.key.inner[1].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.shard_id.inner, shifts[64]);
        let el1 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.key.inner[2].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.key.inner[3].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.value.inner[0].inner, shifts[128]);
        let el2 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.value.inner[1].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.value.inner[2].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.value.inner[3].inner, shifts[128]);
        let el3 = lc.into_num(cs)?;

        Ok([el0, el1, el2, el3])
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, SORTED_STORAGE_LOG_RECORD_ENCODING_LEN>
    for SortedStorageLogItem<E>
{
    fn encode<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; SORTED_STORAGE_LOG_RECORD_ENCODING_LEN], SynthesisError> {
        let packed = self.pack(cs)?;

        Ok(packed)
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, SORTED_STORAGE_LOG_RECORD_ENCODING_LEN>
    for SortedStorageLogItem<E>
{
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, SORTED_STORAGE_LOG_RECORD_ENCODING_LEN>
    for SortedStorageLogItem<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> Shardable<E> for SortedStorageLogItem<E> {
    fn shard_id(&self) -> Byte<E> {
        self.shard_id
    }
}

impl<E: Engine> Addressable<E> for SortedStorageLogItem<E> {
    fn bound_address(&self) -> UInt160<E> {
        self.address
    }
}

// Event structure

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct SortedEventLogItem<E: Engine> {
    pub shard_id: Byte<E>,
    pub tx_number_in_block: UInt16<E>,
    pub address: UInt160<E>,
    pub key: UInt256<E>,
    pub value: UInt256<E>,
}

pub(crate) const SORTED_EVENT_LOG_RECORD_ENCODING_LEN: usize = 4;

pub const SORTED_EVENT_LOG_BYTES: usize = 1 + 2 + 20 + 32 + 32;

impl<E: Engine> SortedEventLogItem<E> {
    pub fn empty() -> Self {
        Self {
            shard_id: Byte::empty(),
            tx_number_in_block: UInt16::zero(),
            address: UInt160::zero(),
            key: UInt256::zero(),
            value: UInt256::zero(),
        }
    }

    pub const CIRCUIT_ENCODING_LEN: usize = SORTED_EVENT_LOG_RECORD_ENCODING_LEN;

    pub fn get_key_derivation_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Byte<E>; SORTED_EVENT_LOG_RECORD_ENCODING_LEN], SynthesisError> {
        let address_bytes = self.address.into_be_bytes(cs)?;
        assert_eq!(address_bytes.len(), 20);
        let key_bytes = self.key.into_be_bytes(cs)?;
        assert_eq!(key_bytes.len(), 32);

        let mut result = vec![];
        result.extend(address_bytes);
        result.extend(key_bytes);

        Ok(result.try_into().unwrap())
    }
}

impl<E: Engine> CSPackable<E, SORTED_EVENT_LOG_RECORD_ENCODING_LEN> for SortedEventLogItem<E> {
    fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; SORTED_EVENT_LOG_RECORD_ENCODING_LEN], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.address.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.key.inner[0].inner, shifts[160]);
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.key.inner[1].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.shard_id.inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.tx_number_in_block.inner, shifts[64 + 8]);
        let el1 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.key.inner[2].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.key.inner[3].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.value.inner[0].inner, shifts[128]);
        let el2 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.value.inner[1].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.value.inner[2].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.value.inner[3].inner, shifts[128]);
        let el3 = lc.into_num(cs)?;

        Ok([el0, el1, el2, el3])
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, SORTED_EVENT_LOG_RECORD_ENCODING_LEN>
    for SortedEventLogItem<E>
{
    fn encode<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; SORTED_EVENT_LOG_RECORD_ENCODING_LEN], SynthesisError> {
        let packed = self.pack(cs)?;

        Ok(packed)
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, SORTED_EVENT_LOG_RECORD_ENCODING_LEN>
    for SortedEventLogItem<E>
{
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, SORTED_EVENT_LOG_RECORD_ENCODING_LEN>
    for SortedEventLogItem<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> Shardable<E> for SortedEventLogItem<E> {
    fn shard_id(&self) -> Byte<E> {
        self.shard_id
    }
}

impl<E: Engine> Addressable<E> for SortedEventLogItem<E> {
    fn bound_address(&self) -> UInt160<E> {
        self.address
    }
}

//pub fn encode_log_item<
//    E: Engine,
//    CS: ConstraintSystem<E>,
//    C: CircuitArithmeticCommitter<E>,
//>(
//    cs: &mut CS,
//    stream: &mut GenericQueueExt<E, C, Byte<E>>,
//    item: &SortedStorageLogItem<E>,
//    apply: &Boolean,
//    encode_rw_flags: bool,
//    encode_shard_flags: bool,
//) -> Result<(), SynthesisError> {
//    encode_into_byte_stream::<_, _, _, _, 20>(cs, stream, &item.actor, apply)?;
//    encode_into_byte_stream::<_, _, _, _, 20>(cs, stream, &item.target, apply)?;
//    encode_into_byte_stream::<_, _, _, _, 32>(cs, stream, &item.key, apply)?;
//    encode_into_byte_stream::<_, _, _, _, 32>(cs, stream, &item.value, apply)?;
//    if encode_rw_flags {
//        encode_constant_length_item_into_byte_stream(cs, stream, &item.r_w_flag, apply)?;
//    }
//    if encode_shard_flags {
//        encode_constant_length_item_into_byte_stream(cs, stream, &item.target_is_zkporter, apply)?;
//    }
//
//    Ok(())
//}
//
//pub fn pack_storage_log_queue<
//    E: Engine,
//    CS: ConstraintSystem<E>,
//    C: CircuitArithmeticCommitter<E>,
//>(
//    cs: &mut CS,
//    sorted_storage_logs_queue: GenericQueueExt<E, C, SortedStorageLogItem<E>>,
//    steam: &mut GenericQueueExt<E, C, Byte<E>>,
//    limit: usize,
//) -> Result<UInt16<E>, SynthesisError> {
//    let total_items = sorted_storage_logs_queue.len();
//    let mut sorted_storage_logs_queue = sorted_storage_logs_queue;
//    for _ in 0..limit {
//        let queue_is_empty = sorted_storage_logs_queue.is_empty(cs)?;
//        let item = sorted_storage_logs_queue.pop_first(cs, &queue_is_empty.not())?;
//        // only encode writes
//        let apply = Boolean::and(cs, &queue_is_empty.not(), &item.r_w_flag)?;
//        encode_log_item(cs, steam, &item, &apply, false, false)?;
//    }
//
//    Ok(total_items)
//}

#[derive(
    Derivative,
    CSWitnessable,
    CSAllocatable,
    CSEqual,
    CSSelectable,
    CSPackable,
    CSEncodable,
    CSDecodable,
)]
#[derivative(Clone, Debug)]
pub struct RollupWriteLogItem<E: Engine> {
    pub key: Bytes32<E>,
    pub value: Bytes32<E>,
}

impl<E: Engine> RollupWriteLogItem<E> {
    pub fn empty() -> Self {
        Self {
            key: Bytes32::empty(),
            value: Bytes32::empty(),
        }
    }
}

pub const ROLLUP_WRITE_LOG_ITEM_ENCODING_LEN: usize = 32 + 32;

impl<E: Engine> IntoBytes<E> for RollupWriteLogItem<E> {
    fn encoding_len() -> usize {
        ROLLUP_WRITE_LOG_ITEM_ENCODING_LEN
    }
    fn into_be_bytes<CS: ConstraintSystem<E>>(
        &self,
        _cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut result = vec![];
        result.extend_from_slice(&self.key.inner);
        result.extend_from_slice(&self.value.inner);

        assert_eq!(result.len(), Self::encoding_len());

        Ok(result)
    }
}

#[derive(
    Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, FixedLengthEncodableExt,
)]
#[EncodingLength = "STORAGE_LOG_RECORD_ENCODING_LEN"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct StorageLogRecordWithUnderlyingU32<E: Engine> {
    pub address: [UInt32<E>; 5],
    pub key: [UInt32<E>; 8],
    pub read_value: [UInt32<E>; 8],
    pub written_value: [UInt32<E>; 8],
    pub r_w_flag: Boolean,
    pub aux_byte: Byte<E>,
    pub rollback: Boolean,
    pub is_service: Boolean,
    pub shard_id: Byte<E>,
    pub tx_number_in_block: UInt16<E>,
    pub timestamp: UInt32<E>,
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, STORAGE_LOG_RECORD_ENCODING_LEN>
    for StorageLogRecordWithUnderlyingU32<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> StorageLogRecordWithUnderlyingU32<E> {
    pub fn pack<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; STORAGE_LOG_RECORD_ENCODING_LEN], SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.address[0].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.address[1].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.address[2].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.address[3].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.address[4].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.key[0].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.key[1].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.shard_id.inner, shifts[shift]);
        shift += 8;
        lc.add_assign_number_with_coeff(&self.aux_byte.inner, shifts[shift]);
        shift += 8;
        lc.add_assign_boolean_with_coeff(&self.r_w_flag, shifts[shift]);
        shift += 1;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.key[2].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.key[3].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.key[4].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.key[5].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.key[6].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.key[7].inner, shifts[shift]);
        shift += 32;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el1 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.read_value[0].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.read_value[1].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.read_value[2].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.read_value[3].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.read_value[4].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.read_value[5].inner, shifts[shift]);
        shift += 32;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el2 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.written_value[0].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.written_value[1].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.written_value[2].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.written_value[3].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.written_value[4].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.written_value[5].inner, shifts[shift]);
        shift += 32;
        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);
        let el3 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.read_value[6].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.read_value[7].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.written_value[6].inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.written_value[7].inner, shifts[shift]);
        shift += 32;

        lc.add_assign_number_with_coeff(&self.tx_number_in_block.inner, shifts[shift]);
        shift += 16;
        lc.add_assign_number_with_coeff(&self.timestamp.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_boolean_with_coeff(&self.is_service, shifts[shift]);
        shift += 1;
        lc.add_assign_boolean_with_coeff(&self.rollback, shifts[shift]);
        shift += 1;

        //dbg!(shift);
        assert!(shift <= E::Fr::CAPACITY as usize);

        let el4 = lc.into_num(cs)?;

        Ok([el0, el1, el2, el3, el4])
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::testing::*;

    use crate::pairing::bn256::*;

    #[test]
    fn test_storage_log_packing() -> Result<(), SynthesisError> {
        let (mut dummy_cs, committer, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let storage_log_item = StorageLogRecord::empty();
        let _ = storage_log_item.pack(cs)?;

        Ok(())
    }
}
