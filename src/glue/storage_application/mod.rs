use super::*;

pub mod input;
use self::input::*;

use crate::franklin_crypto::plonk::circuit::allocated_num::*;
use crate::franklin_crypto::plonk::circuit::byte::*;
use crate::franklin_crypto::plonk::circuit::hashes_with_tables::blake2s::gadgets::*;
use crate::franklin_crypto::plonk::circuit::Assignment;
use crate::glue::aux_byte_markers::aux_byte_for_storage;
use crate::glue::optimizable_queue::variable_length_hash;
use crate::glue::pubdata_hasher::storage_write_data::InitialStorageWriteData;
use crate::glue::pubdata_hasher::storage_write_data::InitialStorageWriteDataQueue;
use crate::glue::pubdata_hasher::storage_write_data::RepeatedStorageWriteData;
use crate::glue::pubdata_hasher::storage_write_data::RepeatedStorageWriteDataQueue;
use crate::glue::traits::get_vec_witness;
use crate::glue::traits::get_vec_witness_raw;
use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;
use crate::scheduler::queues::StorageLogQueue;
use crate::scheduler::queues::StorageLogRecordWithUnderlyingU32;
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use std::convert::TryInto;

const BLAKE2S_REG_WIDTH: usize = 32;
const MERKLE_TREE_LOG_WIDTH: usize = 256; // 2^256 leaves

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct AsU32x8<E: Engine> {
    pub inner: [UInt32<E>; 8],
}

impl<E: Engine> AsU32x8<E> {
    pub fn zero() -> Self {
        Self {
            inner: [UInt32::zero(); 8],
        }
    }

    #[track_caller]
    pub fn alloc_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 32, 8);
        let mut new = Self::zero();
        for i in 0..8 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            new.inner[i] = UInt32 { inner: allocated };
        }

        Ok(new)
    }

    #[track_caller]
    pub fn alloc_from_biguint<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 32, 8);
        let mut new = Self::zero();
        for i in 0..8 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = UInt32::allocate_from_fe(cs, fe)?;
            new.inner[i] = allocated;
        }

        Ok(new)
    }

    #[track_caller]
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<[u32; 8]>,
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::zero();
        for i in 0..8 {
            let val = value.as_ref().map(|el| el[i]);
            let allocated = UInt32::alloc_from_witness(cs, val)?;
            new.inner[i] = allocated;
        }

        Ok(new)
    }

    pub fn get_value(&self) -> Option<BigUint> {
        let mut base = BigUint::from(0u64);
        let mut shift = 0u32;
        for chunk in self.inner.iter() {
            if let Some(v) = chunk.get_value() {
                base += BigUint::from(v) << shift;
                shift += 32;
            } else {
                return None;
            }
        }
        Some(base)
    }

    #[track_caller]
    pub fn conditionally_select<CS>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut res = Self::zero();
        let iter = itertools::multizip((a.inner.iter(), b.inner.iter(), res.inner.iter_mut()));
        for (a_ch, b_ch, out_ch) in iter {
            *out_ch = UInt32::conditionally_select(cs, flag, &a_ch, &b_ch)?;
        }
        Ok(res)
    }

    #[track_caller]
    pub fn conditionally_replace<CS>(
        &mut self,
        cs: &mut CS,
        flag: &Boolean,
        replacement: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let new = Self::conditionally_select(cs, flag, replacement, &self)?;
        *self = new;
        Ok(())
    }

    #[track_caller]
    pub fn conditionally_reverse<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        left: &Self,
        right: &Self,
    ) -> Result<(Self, Self), SynthesisError> {
        let mut res0 = Self::zero();
        let mut res1 = Self::zero();
        let iter = itertools::multizip((
            left.inner.iter(),
            right.inner.iter(),
            res0.inner.iter_mut(),
            res1.inner.iter_mut(),
        ));
        for (left_ch, right_ch, out0_ch, out1_ch) in iter {
            let (x, y) = UInt32::conditionally_reverse(cs, flag, &left_ch, &right_ch)?;
            *out0_ch = x;
            *out1_ch = y;
        }
        Ok((res0, res1))
    }

    pub fn to_u128x2_form<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        shifts: &[E::Fr],
    ) -> Result<AsU128x2<E>, SynthesisError> {
        let mut res = AsU128x2::zero();
        for (in_chunk, out) in self.inner.chunks(4).zip(res.inner.iter_mut()) {
            let mut lc = LinearCombination::zero();
            let mut shift = 0;
            for elem in in_chunk {
                lc.add_assign_number_with_coeff(&elem.inner, shifts[shift]);
                shift += 32;
            }
            let num = lc.into_num(cs)?;
            *out = UInt128::from_num_unchecked(num);
        }

        Ok(res)
    }

    pub fn to_u64x4_form<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        shifts: &[E::Fr],
    ) -> Result<UInt256<E>, SynthesisError> {
        let mut res = UInt256::zero();
        for (in_chunk, out) in self.inner.chunks(2).zip(res.inner.iter_mut()) {
            let mut lc = LinearCombination::zero();
            let mut shift = 0;
            for elem in in_chunk {
                lc.add_assign_number_with_coeff(&elem.inner, shifts[shift]);
                shift += 32;
            }
            let num = lc.into_num(cs)?;
            *out = UInt64::from_num_unchecked(num);
        }

        Ok(res)
    }
}
pub struct WitnessSubstitutor<E: Engine, T: CSWitnessable<E>> {
    produce_actual_witness: bool,
    wit_arr: Vec<T::Witness>,
    wit_idx: usize,
}

impl<E: Engine, T: CSWitnessable<E>> WitnessSubstitutor<E, T> {
    pub fn new(wit_arr: Option<Vec<T::Witness>>) -> Self {
        WitnessSubstitutor {
            produce_actual_witness: wit_arr.is_some(),
            wit_arr: wit_arr.unwrap_or_default(),
            wit_idx: 0,
        }
    }

    pub fn release_data(mut self) -> Vec<T::Witness> {
        self.wit_arr.drain(self.wit_idx..).collect()
    }

    pub fn get_next_witness(&mut self, execute: &Boolean) -> Option<T::Witness> {
        if !self.produce_actual_witness {
            return None;
        }

        let witness = if let Some(flag) = execute.get_value() {
            if flag {
                let res = self.wit_arr[self.wit_idx].clone();
                self.wit_idx += 1;
                Some(res)
            } else {
                Some(<T as CSWitnessable<E>>::placeholder_witness())
            }
        } else {
            None
        };
        witness
    }
}

fn digest_from_iter<'a, E: Engine, CS: ConstraintSystem<E>, I: Iterator<Item = &'a UInt32<E>>>(
    cs: &mut CS,
    iter: I,
    hash_gadget: &Blake2sGadget<E>,
) -> Result<AsU32x8<E>, SynthesisError> {
    let data: Vec<Num<E>> = iter.map(|x| x.inner.clone()).collect();
    let hash_digest = hash_gadget.digest_words32(cs, &data[..])?;
    let mut raw_array = [UInt32::zero(); 8];
    for (in_elem, out) in hash_digest.into_iter().zip(raw_array.iter_mut()) {
        *out = UInt32::from_num_unchecked(in_elem)
    }

    Ok(AsU32x8 { inner: raw_array })
}

fn bytes_as_u32_le<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: &[Byte<E>],
) -> Result<Vec<UInt32<E>>, SynthesisError> {
    assert!(bytes.len() % 4 == 0);
    let shifts = compute_shifts::<E::Fr>();
    let mut result = Vec::with_capacity(bytes.len() / 4);
    for chunk in bytes.chunks_exact(4) {
        let mut lc = LinearCombination::zero();
        for (idx, el) in chunk.iter().enumerate() {
            lc.add_assign_number_with_coeff(&el.inner, shifts[idx * 8]);
        }
        let as_u32 = UInt32::from_num_unchecked(lc.into_num(cs)?);
        result.push(as_u32);
    }

    Ok(result)
}

pub fn storage_applicator_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<StorageApplicationCircuitInstanceWitness<E>>,
    round_function: &R,
    params: (usize, bool),
) -> Result<AllocatedNum<E>, SynthesisError> {
    let (limit, use_blake2s_additional_tables) = params;
    use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
    use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    let columns3 = vec![
        PolyIdentifier::VariablesPolynomial(0),
        PolyIdentifier::VariablesPolynomial(1),
        PolyIdentifier::VariablesPolynomial(2),
    ];

    if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
        let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            BitwiseLogicTable::new(&name, 8),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(bitwise_logic_table)?;
    };

    inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    assert!(limit <= u32::MAX as usize);
    let shifts = compute_shifts::<E::Fr>();
    let blake2s_gadget = Blake2sGadget::new(cs, use_blake2s_additional_tables)?;

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let storage_queue_witness = project_ref!(witness, storage_queue_witness).cloned();
    let mut merkle_paths_wit = project_ref!(witness, merkle_paths).cloned();

    // let flatten_paths_wit = merkle_paths_wit.map(|x| x.into_iter().flatten().collect::<Vec<_>>());
    // let mut merkle_path_wit_substitutor = WitnessSubstitutor::<E, UInt256<E>>::new(flatten_paths_wit);
    let mut leaf_indexes_wit = project_ref!(witness, leaf_indexes_for_reads).cloned();
    // let mut idx_wit_substitutor = WitnessSubstitutor::<E, UInt64<E>>::new(leaf_indxes_wit);

    let mut structured_input = StorageApplicationCycleInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    )?;
    let start_flag = structured_input.start_flag;

    let merkle_root_raw = <[UInt128<E>; 2]>::conditionally_select(
        cs,
        &start_flag,
        &structured_input.observable_input.initial_root,
        &structured_input.hidden_fsm_input.root_hash,
    )?;
    let mut merkle_root = AsU128x2 {
        inner: merkle_root_raw,
    };
    let shard = structured_input.observable_input.shard;
    let mut next_free_idx = UInt64::<E>::conditionally_select(
        cs,
        &start_flag,
        &structured_input
            .observable_input
            .initial_next_enumeration_counter,
        &structured_input.hidden_fsm_input.next_enumeration_counter,
    )?;

    let storage_queue_from_input = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .storage_application_log_state
            .head_state,
        structured_input
            .observable_input
            .storage_application_log_state
            .tail_state,
        structured_input
            .observable_input
            .storage_application_log_state
            .num_items,
    )?;
    // it must be trivial
    storage_queue_from_input
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let storage_queue_from_fsm = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_storage_application_log_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .current_storage_application_log_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .current_storage_application_log_state
            .num_items,
    )?;

    let mut storage_accesses_queue = StorageLogQueue::conditionally_select(
        cs,
        &start_flag,
        &storage_queue_from_input,
        &storage_queue_from_fsm,
    )?;

    if let Some(wit) = storage_queue_witness {
        storage_accesses_queue.witness = wit;
    }

    let initial_writes_queue_state = FixedWidthEncodingGenericQueueState::conditionally_select(
        cs,
        &start_flag,
        &FixedWidthEncodingGenericQueueState::empty(),
        &structured_input
            .hidden_fsm_input
            .initial_writes_pubdata_queue_state,
    )?;
    let mut initial_writes_queue =
        InitialStorageWriteDataQueue::from_state(cs, initial_writes_queue_state)?;

    let repeated_writes_queue_state = FixedWidthEncodingGenericQueueState::conditionally_select(
        cs,
        &start_flag,
        &FixedWidthEncodingGenericQueueState::empty(),
        &structured_input
            .hidden_fsm_input
            .repeated_writes_pubdata_queue_state,
    )?;
    let mut repeated_writes_queue =
        RepeatedStorageWriteDataQueue::from_state(cs, repeated_writes_queue_state)?;

    let mut second_iter_in_progress = Boolean::constant(false);
    let mut full_key = AsU128x2::zero();
    let mut index = UInt64::zero();
    let mut saved_written_value = [UInt32::<E>::zero(); 8];
    let mut completed = storage_accesses_queue.is_empty(cs)?;

    let mut merkle_path: [AsU32x8<E>; MERKLE_TREE_LOG_WIDTH] =
        [AsU32x8::<E>::zero(); MERKLE_TREE_LOG_WIDTH];

    for (_is_first, is_last, _cycle) in (0..limit).identify_first_last() {
        // if this is the last executing cycle - we do not start the parsing of the new element:
        // instead we either complete the second iter of processing of the last element or simply do nothing
        let (should_compare_roots, parse_next_queue_elem) = if !is_last {
            let should_compare_roots = completed.not();
            let parse_next_queue_elem =
                Boolean::and(cs, &should_compare_roots, &second_iter_in_progress.not())?;

            (should_compare_roots, parse_next_queue_elem)
        } else {
            (Boolean::constant(false), Boolean::constant(false))
        };

        let storage_log =
            storage_accesses_queue.pop_first(cs, &parse_next_queue_elem, round_function)?;
        let StorageLogRecord {
            address,
            key,
            read_value,
            written_value,
            r_w_flag,
            shard_id,
            ..
        } = storage_log;

        let shard_is_valid = Num::equals(cs, &shard_id.inner, &shard.inner)?;
        let aux_byte_is_valid = Num::equals(
            cs,
            &storage_log.aux_byte.inner,
            &aux_byte_for_storage().inner,
        )?;
        let is_valid = Boolean::and(cs, &shard_is_valid, &aux_byte_is_valid)?;
        can_not_be_false_if_flagged(cs, &is_valid, &parse_next_queue_elem)?;

        // compute index of a leaf (full_key) as Blakes2s(address || key)
        let address_bytes = address.into_be_bytes(cs)?;
        let address_as_u32 = bytes_as_u32_le(cs, &address_bytes)?;
        let mut extended_address_as_u32 = vec![UInt32::zero(); 3]; // we extend to 32 bytes
        extended_address_as_u32.extend(address_as_u32);

        let key_bytes = key.into_be_bytes(cs)?;
        let key_as_u32 = bytes_as_u32_le(cs, &key_bytes)?;

        assert_eq!(extended_address_as_u32.len(), 8);
        assert_eq!(key_as_u32.len(), 8);

        let leaf_index = digest_from_iter(
            cs,
            extended_address_as_u32.iter().chain(key_as_u32.iter()),
            &blake2s_gadget,
        )?;
        let computed_full_key = leaf_index.to_u128x2_form(cs, &shifts[..])?;
        full_key.conditionally_replace(cs, &parse_next_queue_elem, &computed_full_key)?;

        // we are going to git the full bit decomposition of full key
        let mut path_selectors = full_key.inner[0]
            .inner
            .into_bits_le(cs, Some(MERKLE_TREE_LOG_WIDTH / 2))?;
        path_selectors.extend_from_slice(
            &full_key.inner[1]
                .inner
                .into_bits_le(cs, Some(MERKLE_TREE_LOG_WIDTH / 2))?[..],
        );
        let path_selectors: [_; 256] = path_selectors.try_into().unwrap();

        // compute the hash of the leaf as Blake2s(index | leaf_value)
        // range check for index will be done later when we split index into two 32-bit words
        let read_index_wit = if parse_next_queue_elem.get_value().unwrap_or(false) {
            let next = get_vec_witness_raw(&mut leaf_indexes_wit, 0);

            next
        } else {
            Some(0)
        };
        let read_index = UInt64::alloc_from_witness(cs, read_index_wit)?;
        index.conditionally_replace(cs, &parse_next_queue_elem, &read_index)?;

        // determine whether we need to increment enumeration index
        let idx_is_zero = index.is_zero(cs)?;
        let should_assign_fresh_idx = Boolean::and(cs, &second_iter_in_progress, &idx_is_zero)?;
        index.conditionally_replace(cs, &should_assign_fresh_idx, &next_free_idx)?;
        next_free_idx =
            next_free_idx.conditionally_increment_unchecked(cs, &should_assign_fresh_idx)?;

        // decompose whatever we did get from the queue
        let read_value_bytes = read_value.into_be_bytes(cs)?;
        let read_value_as_u32 = bytes_as_u32_le(cs, &read_value_bytes)?;
        let written_value_bytes = written_value.into_be_bytes(cs)?;
        let written_value_as_u32 = bytes_as_u32_le(cs, &written_value_bytes)?;

        // leaf = if second_iter_in_progress { saved_val } else { read_val }
        // saved_val := written_val;
        let mut leaf_value = AsU32x8::zero();
        let iter = itertools::multizip((
            read_value_as_u32.iter(),
            written_value_as_u32.iter(),
            leaf_value.inner.iter_mut(),
            saved_written_value.iter_mut(),
        ));
        for (read_chunk, written_chunk, out, saved_written_chunk_chunk) in iter {
            *out = UInt32::conditionally_select(
                cs,
                &second_iter_in_progress,
                &saved_written_chunk_chunk,
                &read_chunk,
            )?;
            *saved_written_chunk_chunk = written_chunk.clone();
        }

        let idx_bytes = index.into_be_bytes(cs)?;
        assert_eq!(idx_bytes.len(), 8);
        let idx_chunks = bytes_as_u32_le(cs, &idx_bytes)?;
        assert_eq!(idx_chunks.len(), 2);
        idx_chunks[0].inner.enforce_equal(cs, &Num::zero())?; // top part is always empty in observable future
        let mut cur_hash = digest_from_iter(
            cs,
            idx_chunks.iter().chain(leaf_value.inner.iter()),
            &blake2s_gadget,
        )?;

        let current_round_path_wit = if parse_next_queue_elem.get_value().unwrap_or(false) {
            let current = get_vec_witness_raw(&mut merkle_paths_wit, vec![[0u32; 8]; 256]);
            let current = current.map(|el| el.try_into().unwrap());

            current
        } else {
            Some([[0u32; 8]; 256])
        };

        for (i, path_bit) in path_selectors.iter().enumerate() {
            let this_layer_set = current_round_path_wit.as_ref().map(|el| el[i]);
            let new_merkle_path_component = AsU32x8::alloc(cs, this_layer_set)?;
            merkle_path[i].conditionally_replace(
                cs,
                &parse_next_queue_elem,
                &new_merkle_path_component,
            )?;
            let (left, right) =
                AsU32x8::conditionally_reverse(cs, path_bit, &cur_hash, &merkle_path[i])?;
            cur_hash = digest_from_iter(
                cs,
                left.inner.iter().chain(right.inner.iter()),
                &blake2s_gadget,
            )?;
        }
        // in case of read: merkle_root == computed_merkle_root == new_merkle_root
        // new_merkle_root = select(if is_write: then new_merkle_root else computed_merkle_root);
        // so we first compute merkle_root - either the old one or the selected one and then enforce equality
        let computed_merkle_root = cur_hash.to_u128x2_form(cs, &shifts[..])?;
        merkle_root.conditionally_replace(cs, &second_iter_in_progress, &computed_merkle_root)?;
        AsU128x2::conditionally_enforce_equal(
            cs,
            &should_compare_roots,
            &merkle_root,
            &computed_merkle_root,
        )?;

        // fill the output queues:
        let should_write_to_init_storage_writes_queue =
            Boolean::and(cs, &idx_is_zero, &second_iter_in_progress)?;
        let should_write_to_rep_storage_writes_queue =
            Boolean::and(cs, &idx_is_zero.not(), &second_iter_in_progress)?;

        let mut full_key_bytes = vec![];
        for el in full_key.inner.iter() {
            let bytes_le = el.into_le_bytes(cs)?;
            full_key_bytes.extend(bytes_le);
        }
        let full_key_bytes: [_; 32] = full_key_bytes.try_into().unwrap();

        let mut leaf_value_bytes = vec![];
        for el in leaf_value.inner.iter() {
            let bytes_le = el.into_le_bytes(cs)?;
            leaf_value_bytes.extend(bytes_le);
        }
        let leaf_value_bytes: [_; 32] = leaf_value_bytes.try_into().unwrap();

        let queue_elem = InitialStorageWriteData::<E>::new(full_key_bytes, leaf_value_bytes);
        initial_writes_queue.push(
            cs,
            &queue_elem,
            &should_write_to_init_storage_writes_queue,
            round_function,
        )?;

        let queue_elem = RepeatedStorageWriteData::<E>::new(index.clone(), leaf_value_bytes);
        repeated_writes_queue.push(
            cs,
            &queue_elem,
            &should_write_to_rep_storage_writes_queue,
            round_function,
        )?;

        // toggle control flags
        let input_queue_is_empty = storage_accesses_queue.is_empty(cs)?;
        // cur elem is processed only in the case second iter in progress or r_w_flag is false;
        let cur_elem_is_processed = Boolean::or(cs, &second_iter_in_progress, &r_w_flag.not())?;
        let completed_now = Boolean::and(cs, &input_queue_is_empty, &cur_elem_is_processed)?;
        completed = Boolean::or(cs, &completed, &completed_now)?;
        second_iter_in_progress = Boolean::and(cs, &parse_next_queue_elem, &r_w_flag)?;
    }

    structured_input.completion_flag = completed.clone();
    let storage_queue_state = storage_accesses_queue.into_state();
    let repeated_writes_queue_state = repeated_writes_queue.into_state();
    let initial_writes_queue_state = initial_writes_queue.into_state();

    let fsm_output = StorageApplicationFSM::<E> {
        root_hash: merkle_root.inner.clone(),
        shard: shard.clone(),
        next_enumeration_counter: next_free_idx.clone(),
        current_storage_application_log_state: storage_queue_state.clone(),
        repeated_writes_pubdata_queue_state: repeated_writes_queue_state.clone(),
        initial_writes_pubdata_queue_state: initial_writes_queue_state.clone(),
    };
    structured_input.hidden_fsm_output = fsm_output;

    let observable_output = StorageApplicationOutputData::<E> {
        final_next_enumeration_counter: next_free_idx,
        final_root: merkle_root.inner,
        repeated_writes_pubdata_queue_state: repeated_writes_queue_state,
        initial_writes_pubdata_queue_state: initial_writes_queue_state,
    };
    let observable_output = StorageApplicationOutputData::conditionally_select(
        cs,
        &structured_input.completion_flag,
        &observable_output,
        &StorageApplicationOutputData::empty(),
    )?;
    structured_input.observable_output = observable_output;

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = structured_input_witness {
            assert_eq!(circuit_result, passed_input);
        }
    }

    use crate::inputs::ClosedFormInputCompactForm;
    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    // dbg!(compact_form.create_witness());
    use crate::glue::optimizable_queue::commit_encodable_item;
    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();
    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;

    Ok(public_input)
}
