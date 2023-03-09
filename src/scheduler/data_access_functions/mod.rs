use super::*;

pub use super::queues::storage_log::StorageLogRecord;
use crate::glue::aux_byte_markers::*;
use crate::vm::primitives::*;

// // We assume that the first class citizen token looks like:
// // mapping user_address => uint256 balance
// // ....

// // so for a key that is derived on [0] (first storage slot declaration) and u32 (address of the token) we should read some value
// // in the user_address account

// // in the storage log we have
// // - writer (in this case address of the contract)
// // - write_dst (in this case - user_address)
// // - key - in our case == 0

// // so we just make a storage log in such format

// pub fn partial_storage_log_for_first_class_balance<E: Engine>(
//     account_address: SmallFixedWidthInteger<E, U160>,
//     token_address: SmallFixedWidthInteger<E, U160>,
//     account_is_zkporter: Boolean,
// ) -> StorageLogRecord<E> {
//     StorageLogRecord::<E> {
//         actor: token_address.to_u160(),
//         target: account_address.to_u160(),
//         key: UInt256::zero(),
//         read_value: UInt256::zero(), // we do not need it yet
//         written_value: UInt256::zero(),
//         r_w_flag: Boolean::Constant(false),
//         aux_byte: aux_byte_for_storage(),
//         is_service: Boolean::Constant(false),
//         rollback: Boolean::Constant(false),
//         target_is_zkporter: account_is_zkporter,
//         tx_number_in_block: UInt16::zero(),
//         monotonic_counter_in_tx: UInt16::zero(),
//     }
// }

// pub fn special_purpose_account<E: Engine>() -> UInt160<E> {
//     UInt160::zero()
// }

// pub fn shard_id_actor_account<E: Engine>() -> SmallFixedWidthInteger<E, U160> {
//     SmallFixedWidthInteger::constant_from_u128(0u128)
// }

// pub fn code_hash_storage_actor_account<E: Engine>() -> SmallFixedWidthInteger<E, U160> {
//     SmallFixedWidthInteger::constant_from_u128(1u128)
// }

// pub fn account_aux_data_key<E: Engine>() -> UInt256<E> {
//     UInt256::zero()
// }

// pub fn account_code_root_hash_key<E: Engine>() -> UInt256<E> {
//     UInt256::constant_from_biguint(BigUint::from(1u64))
// }

// pub fn account_schnorr_pubkey_hash_key<E: Engine>() -> UInt256<E> {
//     UInt256::constant_from_biguint(BigUint::from(2u64))
// }

// // we would have two options here:
// // - use a special key >= E::Fr::char()
// // - use a special purpose account
// // for now we stick for the latter

// pub fn partial_storage_log_for_account_packed_aux_data<E: Engine>(
//     account_address: UInt160<E>,
//     target_is_zkporter: Boolean,
// ) -> StorageLogRecord<E> {
//     StorageLogRecord::<E> {
//         actor: special_purpose_account(),
//         target: account_address,
//         key: account_aux_data_key(),
//         read_value: UInt256::zero(), // we do not need it yet
//         written_value: UInt256::zero(),
//         r_w_flag: Boolean::Constant(false),
//         aux_byte: aux_byte_for_storage(),
//         is_service: Boolean::Constant(true),
//         rollback: Boolean::Constant(false),
//         target_is_zkporter,
//         tx_number_in_block: UInt16::zero(),
//         monotonic_counter_in_tx: UInt16::zero(),
//     }
// }

// pub fn partial_storage_log_for_account_code_root_hash<E: Engine>(
//     account_address: UInt160<E>,
//     target_is_zkporter: Boolean
// ) -> StorageLogRecord<E> {
//     StorageLogRecord::<E> {
//         actor: special_purpose_account(),
//         target: account_address,
//         key: account_code_root_hash_key(),
//         read_value: UInt256::zero(), // we do not need it yet
//         written_value: UInt256::zero(),
//         r_w_flag: Boolean::Constant(false),
//         aux_byte: aux_byte_for_storage(),
//         is_service: Boolean::Constant(false),
//         rollback: Boolean::Constant(false),
//         target_is_zkporter,
//         tx_number_in_block: UInt16::zero(),
//         monotonic_counter_in_tx: UInt16::zero(),
//     }
// }

// pub fn partial_storage_log_for_account_schnorr_pubkey_hash<E: Engine>(
//     account_address: UInt160<E>,
//     target_is_zkporter: Boolean,
// ) -> StorageLogRecord<E> {
//     StorageLogRecord::<E> {
//         actor: special_purpose_account(),
//         target: account_address,
//         key: account_schnorr_pubkey_hash_key(),
//         read_value: UInt256::zero(), // we do not need it yet
//         written_value: UInt256::zero(),
//         r_w_flag: Boolean::Constant(false),
//         aux_byte: aux_byte_for_storage(),
//         is_service: Boolean::Constant(false),
//         rollback: Boolean::Constant(false),
//         target_is_zkporter,
//         tx_number_in_block: UInt16::zero(),
//         monotonic_counter_in_tx: UInt16::zero(),
//     }
// }

// // here we hash the tuple (writer, key) to get a well distributed key
// pub fn partial_storage_log_into_raw_key<
//     E: Engine,
//     CS: ConstraintSystem<E>,
//     R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
//     const AWIDTH: usize,
//     const SWIDTH: usize
// >(
//     cs: &mut CS,
//     log: &StorageLogRecord<E>,
//     round_function: &R
// ) -> Result<UInt256<E>, SynthesisError> {
//     let t = log.get_tuple_for_key_derivation(cs)?;
//     let commitment = variable_length_hash_with_rescue_prime_padding(cs, &t, round_function)?;
//     let key = UInt256::canonical_from_num(cs, &commitment)?;

//     Ok(key)
// }

// pub fn partial_storage_log_for_shard_id<E: Engine, CS: ConstraintSystem<E>>(
//     cs: &mut CS,
//     account_address: UInt160<E>,
// ) -> Result<StorageLogRecord<E>, SynthesisError> {
//     use crate::scheduler::circuit::data_structs::*;
//     let address_as_u256 = address_to_u256(cs, &account_address)?;

//     let record = StorageLogRecord::<E> {
//         actor: shard_id_actor_account().to_u160(),
//         target: special_purpose_account(),
//         key: address_as_u256,
//         read_value: UInt256::zero(), // we do not need it yet
//         written_value: UInt256::zero(),
//         r_w_flag: Boolean::Constant(false),
//         aux_byte: aux_byte_for_storage(),
//         is_service: Boolean::Constant(true),
//         rollback: Boolean::Constant(false),
//         target_is_zkporter: Boolean::Constant(false),
//         tx_number_in_block: UInt16::zero(),
//         monotonic_counter_in_tx: UInt16::zero(),
//     };

//     Ok(record)
// }

// pub fn partial_storage_log_for_global_codehash_storage<E: Engine>(
//     code_hash: UInt256<E>
// ) -> StorageLogRecord<E> {
//     StorageLogRecord::<E> {
//         actor: code_hash_storage_actor_account().to_u160(),
//         target: special_purpose_account(),
//         key: code_hash,
//         read_value: UInt256::zero(), // we do not need it yet
//         written_value: UInt256::zero(),
//         r_w_flag: Boolean::Constant(false),
//         aux_byte: aux_byte_for_storage(),
//         is_service: Boolean::Constant(true),
//         rollback: Boolean::Constant(false),
//         target_is_zkporter: Boolean::Constant(false),
//         tx_number_in_block: UInt16::zero(),
//         monotonic_counter_in_tx: UInt16::zero(),
//     }
// }

// pub fn partial_storage_log_for_key_derivation<E: Engine>(
//     actor: UInt160<E>,
//     key: UInt256<E>,
// ) -> StorageLogRecord<E> {
//     StorageLogRecord::<E> {
//         actor: actor,
//         target: SmallFixedWidthInteger::zero().to_u160(),
//         key,
//         read_value: UInt256::zero(),
//         written_value: UInt256::zero(),
//         r_w_flag: Boolean::Constant(false),
//         aux_byte: aux_byte_for_storage(),
//         is_service: Boolean::Constant(true),
//         rollback: Boolean::Constant(false),
//         target_is_zkporter: Boolean::Constant(false),
//         tx_number_in_block: UInt16::zero(),
//         monotonic_counter_in_tx: UInt16::zero(),
//     }
// }

// // Derives storage key following storage log conventions
// pub fn derive_storage_slot_key_from_partial_log<
//     E: Engine,
//     CS: ConstraintSystem<E>,
//     R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
//     const AWIDTH: usize,
//     const SWIDTH: usize,
//     const SDEPTH: usize,
// >(
//     cs: &mut CS,
//     log_item: &StorageLogRecord<E>,
//     round_function: &R,
// ) -> Result<[Boolean; SDEPTH], SynthesisError> {
//     let derived_key = partial_storage_log_into_raw_key(cs, &log_item, round_function)?;

//     let [lo, hi] = derived_key.into_u128_pair(cs)?;
//     let low_bits = lo.inner.into_bits_le(cs, Some(128))?;
//     let high_bits = hi.inner.into_bits_le(cs, Some(128))?;

//     let mut key_bits = [Boolean::constant(false); SDEPTH];

//     for (dst, src) in key_bits
//         .iter_mut()
//         .zip(low_bits.into_iter().chain(high_bits.into_iter()))
//         {
//             *dst = src
//         }

//     Ok(key_bits)
// }

use std::collections::HashMap;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct StorageWitnessHelper {
    // shard_id, address, key into value
    inner: HashMap<u8, HashMap<BigUint, HashMap<BigUint, BigUint>>>,
}

impl StorageWitnessHelper {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }
    pub fn populate_initial_values(&mut self, witness: Vec<(u8, BigUint, BigUint, BigUint)>) {
        for (shard_id, address, key, value) in witness.into_iter() {
            let shard_subspace = self.inner.entry(shard_id).or_default();
            let address_subspace = shard_subspace.entry(address).or_default();
            address_subspace.insert(key.clone(), value);
        }
    }

    #[track_caller]
    pub fn read(&self, shard_id: u8, address: &BigUint, key: &BigUint) -> BigUint {
        if let Some(shard_subspace) = self.inner.get(&shard_id) {
            if let Some(address_subspace) = shard_subspace.get(address) {
                if let Some(value) = address_subspace.get(key).cloned() {
                    return value;
                }
            }
        }

        BigUint::from(0u64)
    }

    #[track_caller]
    pub fn write(&mut self, shard_id: u8, address: BigUint, key: BigUint, value: BigUint) {
        let shard_subspace = self.inner.entry(shard_id).or_default();
        let address_subspace = shard_subspace.entry(address).or_default();
        address_subspace.insert(key.clone(), value);
    }

    fn storage_log_into_addressing_tuple_and_new_value<E: Engine>(
        record: &StorageLogRecord<E>,
    ) -> Option<(u8, BigUint, BigUint, BigUint)> {
        match (
            record.shard_id.get_byte_value(),
            record.address.get_value(),
            record.key.get_value(),
            record.written_value.get_value(),
        ) {
            (Some(shard_id), Some(address), Some(key), Some(new_value)) => {
                let address = address.into();
                let t = (shard_id, address, key, new_value);

                Some(t)
            }
            _ => None,
        }
    }

    pub fn read_for_storage_log<E: Engine>(&self, record: &StorageLogRecord<E>) -> Option<BigUint> {
        if let Some(t) = Self::storage_log_into_addressing_tuple_and_new_value(record) {
            let (shard_id, address, key, _) = t;
            if let Some(rw) = record.r_w_flag.get_value() {
                assert_eq!(rw, false, "we expect record to be a reading one");
            }

            let value = self.read(shard_id, &address, &key);

            Some(value)
        } else {
            None
        }
    }

    pub fn write_for_storage_log<E: Engine>(&mut self, record: &StorageLogRecord<E>) {
        if let Some(t) = Self::storage_log_into_addressing_tuple_and_new_value(record) {
            let (shard_id, address, key, new_value) = t;
            if let Some(rw) = record.r_w_flag.get_value() {
                assert_eq!(rw, true, "we expect record to be a writing one");
            }
            self.write(shard_id, address, key, new_value);
        }
    }
}

// pub fn contract_data_into_address<
//     E: Engine,
//     CS: ConstraintSystem<E>,
//     R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
//     const AWIDTH: usize,
//     const SWIDTH: usize
// >(
//     cs: &mut CS,
//     deployer: &UInt160<E>,
//     code_root_hash: &UInt256<E>,
//     salt: &UInt256<E>,
//     target_is_zkporter: &Boolean,
//     round_function: &R
// ) -> Result<(UInt256<E>, UInt160<E>), SynthesisError> {
//     // for future we represent an address as a full 32 byte word
//     use crate::scheduler::circuit::data_structs::address_to_u256;

//     // here we follow the agreement of how hashing works in the VM for bytes32
//     let address_as_u256 = address_to_u256(cs, &deployer)?;
//     let shifts = compute_shifts::<E::Fr>();

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_number_with_coeff(&address_as_u256.inner[0].inner, shifts[0]);
//     lc.add_assign_number_with_coeff(&address_as_u256.inner[1].inner, shifts[64]);
//     let el0 = lc.into_num(cs)?;

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_number_with_coeff(&address_as_u256.inner[2].inner, shifts[0]);
//     lc.add_assign_number_with_coeff(&address_as_u256.inner[3].inner, shifts[64]);
//     let el1 = lc.into_num(cs)?;

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_number_with_coeff(&code_root_hash.inner[0].inner, shifts[0]);
//     lc.add_assign_number_with_coeff(&code_root_hash.inner[1].inner, shifts[64]);
//     let el2 = lc.into_num(cs)?;

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_number_with_coeff(&code_root_hash.inner[2].inner, shifts[0]);
//     lc.add_assign_number_with_coeff(&code_root_hash.inner[3].inner, shifts[64]);
//     let el3 = lc.into_num(cs)?;

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_number_with_coeff(&salt.inner[0].inner, shifts[0]);
//     lc.add_assign_number_with_coeff(&salt.inner[1].inner, shifts[64]);
//     let el4 = lc.into_num(cs)?;

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_number_with_coeff(&salt.inner[2].inner, shifts[0]);
//     lc.add_assign_number_with_coeff(&salt.inner[3].inner, shifts[64]);
//     let el5 = lc.into_num(cs)?;

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_boolean_with_coeff(&target_is_zkporter, shifts[0]);
//     let el6 = lc.into_num(cs)?;

//     let t = [el0, el1, el2, el3, el4, el5, el6, Num::zero()];
//     let commitment = variable_length_hash_with_rescue_prime_padding(cs, &t, round_function)?;
//     let key = UInt256::canonical_from_num(cs, &commitment)?;

//     // now we have to convert it back into the address by trimming highest bytes
//     let ll = key.inner[0];
//     let lh = key.inner[1];

//     let tmp = key.inner[2];
//     let chunks = tmp.decompose_into_uint16_in_place(cs)?;

//     let mut lc = LinearCombination::zero();
//     lc.add_assign_number_with_coeff(&ll.inner, shifts[0]);
//     lc.add_assign_number_with_coeff(&lh.inner, shifts[64]);
//     lc.add_assign_number_with_coeff(&chunks[0].inner, shifts[128]);
//     lc.add_assign_number_with_coeff(&chunks[1].inner, shifts[128 + 16]);
//     let tmp = lc.into_num(cs)?;
//     let address = UInt160::from_num_unchecked(tmp);

//     let extended_address = address_to_u256(cs, &address)?;

//     Ok((extended_address, address))
// }
