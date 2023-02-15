use super::*;

use super::input::*;
use crate::glue::optimizable_queue::FixedWidthEncodingGenericQueue;
use crate::glue::pubdata_hasher::storage_write_data::ByteSerializable;
use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::*;

pub fn hash_pubdata_entry_point_variable_length<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const N: usize,
    const SERIALIZATION_WIDTH: usize,
    I: CircuitFixedLengthEncodableExt<E, N>
        + CircuitFixedLengthDecodableExt<E, N>
        + ByteSerializable<E, SERIALIZATION_WIDTH>,
>(
    cs: &mut CS,
    witness: Option<PubdataHasherInstanceWitness<E, N, SERIALIZATION_WIDTH, I>>,
    round_function: &R,
    limit: usize,
) -> Result<AllocatedNum<E>, SynthesisError> {
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

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let input_queue_witness = project_ref!(witness, input_queue_witness).cloned();

    let mut structured_input =
        PubdataHasherInputOutput::alloc_ignoring_outputs(cs, structured_input_witness.clone())?;

    Boolean::enforce_equal(cs, &structured_input.start_flag, &Boolean::constant(true))?;

    let mut initial_queue = FixedWidthEncodingGenericQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .input_queue_state
            .head_state,
        structured_input
            .observable_input
            .input_queue_state
            .tail_state,
        structured_input
            .observable_input
            .input_queue_state
            .num_items,
    )?;

    if let Some(wit) = input_queue_witness {
        initial_queue.witness = wit;
    }

    let (pubdata_hash_as_bytes32, _) =
        hash_pubdata_inner(cs, initial_queue, round_function, limit)?;

    // form the final state
    structured_input.observable_output = PubdataHasherOutputData::empty();
    structured_input.observable_output.pubdata_hash = pubdata_hash_as_bytes32;
    structured_input.completion_flag = Boolean::constant(true);

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

pub fn hash_pubdata_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const N: usize,
    const SERIALIZATION_WIDTH: usize,
    I: CircuitFixedLengthEncodableExt<E, N>
        + CircuitFixedLengthDecodableExt<E, N>
        + ByteSerializable<E, SERIALIZATION_WIDTH>,
>(
    cs: &mut CS,
    mut initial_queue: FixedWidthEncodingGenericQueue<E, I, N>,
    round_function: &R,
    limit: usize,
) -> Result<(Bytes32<E>, (UInt32<E>, Vec<Byte<E>>)), SynthesisError> {
    let reused_table_name =
        crate::franklin_crypto::plonk::circuit::tables::RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME;

    let keccak_gadget = Keccak256Gadget::new(cs, None, None, None, None, true, &reused_table_name)?;

    // we can precompute special case, which is empty input queue,
    // so we will hash 4x0 bytes

    use sha3::Digest;
    let empty_input_hash = sha3::Keccak256::digest(&[0u8; 4]);
    let mut byte_array = [0u8; 32];
    byte_array.copy_from_slice(empty_input_hash.as_slice());
    let empty_output_hash = Bytes32::<E>::constant_from_bytes(&byte_array);

    let empty_pubdata = initial_queue.is_empty(cs)?;

    let num_items = initial_queue.len();
    let num_items_bytes = num_items.into_be_bytes(cs)?;
    assert_eq!(num_items_bytes.len(), 4);

    let mut raw_items_bytes = vec![];
    raw_items_bytes.extend_from_slice(&num_items_bytes);

    let mut round_buffer = vec![]; // round buffer for keccak
    round_buffer.extend(num_items_bytes);

    let mut keccak_state = [Num::<E>::zero(); 25];

    let mut buffer_if_we_pad = [UInt64::<E>::zero(); 17];

    let mut completed = Boolean::constant(false);

    let mut output_completed = Boolean::constant(false);

    let mut output_words = [UInt64::zero(); 4];

    for _round in 0..limit {
        // theoretically we would pop from the queue, serialize and absorb into sponge.
        // As sponge rate is not multiple of serialization width, we have to manually maintain a buffer
        // and a small FSM to drive absorbtion and padding

        let can_pop = initial_queue.is_empty(cs)?.not();
        let item = initial_queue.pop_first(cs, &can_pop, round_function)?;
        let mut serialized = item.serialize(cs)?;
        // explicit cleanup
        for dst in serialized.iter_mut() {
            *dst = Byte::conditionally_select(cs, &can_pop, &*dst, &Byte::zero())?;
        }
        raw_items_bytes.extend_from_slice(&serialized);

        let e = initial_queue.is_empty(cs)?;
        let done = smart_and(cs, &[can_pop, e])?; // check if it was last item

        // two options:
        // - current item is trivial, then we can pad the buffer and mark it to use for the next time when
        // we invoke round function
        // - item is non-trivial, so we add it into the buffer

        assert!(round_buffer.len() < 136);

        let mut buffer_with_current_item = round_buffer.clone();
        buffer_with_current_item.extend(serialized);

        if buffer_with_current_item.len() >= 136 {
            // we should run round function

            let mut current_keccak_state = KeccakState::from_raw(keccak_state);
            current_keccak_state.base = KeccakStateBase::Binary;

            let buffer_for_round = buffer_with_current_item[..136].to_vec();
            let carry_on = buffer_with_current_item[136..].to_vec();

            let mut buffer_as_u64 = vec![];
            for chunk in buffer_for_round.chunks(8) {
                let chunk: [_; 8] = chunk.to_vec().try_into().unwrap();
                let as_u64 = UInt64::from_bytes_le(cs, &chunk)?;
                buffer_as_u64.push(as_u64);
            }

            // now we should select either buffer for finalization,
            // or the buffer we just created

            let mut input = vec![];
            assert_eq!(buffer_as_u64.len(), buffer_if_we_pad.len());
            for (this, finalization) in buffer_as_u64.into_iter().zip(buffer_if_we_pad.iter()) {
                let selected = UInt64::conditionally_select(cs, &completed, finalization, &this)?;

                input.push(selected);
            }

            let input: Vec<_> = input.into_iter().map(|el| el.inner).collect();
            let input: [_; 17] = input.try_into().unwrap();

            let state_after_absorb = keccak_gadget.keccak_absorb_into_state_into_binary_base(
                cs,
                current_keccak_state,
                input,
            )?;
            assert!(state_after_absorb.base == KeccakStateBase::First);
            let (new_inner, squeezed) = keccak_gadget
                .keccak_normal_rounds_function_state_in_first_base(cs, state_after_absorb)?;
            assert!(new_inner.base == KeccakStateBase::Binary);

            let squeezed: Vec<_> = squeezed
                .into_iter()
                .map(|el| UInt64::from_num_unchecked(el))
                .collect();
            let squeezed: [_; 4] = squeezed.try_into().unwrap();

            for (dst, src) in output_words.iter_mut().zip(squeezed.into_iter()) {
                *dst = UInt64::conditionally_select(cs, &output_completed, &*dst, &src)?;
            }

            keccak_state = new_inner.into_raw();

            let finished_output = smart_and(cs, &[output_completed.not(), completed])?;
            output_completed = smart_or(cs, &[finished_output, output_completed])?;

            round_buffer = carry_on;
        } else {
            round_buffer = buffer_with_current_item;
        }

        assert!(round_buffer.len() < 136);

        // if it was the last item (and by invariant above) we can do the padding
        let mut buffer_for_last_round = round_buffer.clone();
        let padlen = 136 - buffer_for_last_round.len();
        assert!(padlen > 0);
        assert!(padlen != 1);
        let zeroes_to_add = padlen - 2;
        buffer_for_last_round.push(Byte::constant(0x01));
        buffer_for_last_round.extend(vec![Byte::zero(); zeroes_to_add]);
        buffer_for_last_round.push(Byte::constant(0x80));

        assert_eq!(buffer_for_last_round.len(), 136);

        let mut buffer_for_last_round_as_u64 = vec![];
        for chunk in buffer_for_last_round.chunks(8) {
            let chunk: [_; 8] = chunk.to_vec().try_into().unwrap();
            let as_u64 = UInt64::from_bytes_le(cs, &chunk)?;
            buffer_for_last_round_as_u64.push(as_u64);
        }

        assert_eq!(buffer_for_last_round_as_u64.len(), 17);

        for (dst, src) in buffer_if_we_pad
            .iter_mut()
            .zip(buffer_for_last_round_as_u64.into_iter())
        {
            *dst = UInt64::conditionally_select(cs, &done, &src, &*dst)?;
        }

        completed = smart_or(cs, &[completed, done])?;
    }

    // final run if we have something left
    {
        let mut current_keccak_state = KeccakState::from_raw(keccak_state);
        current_keccak_state.base = KeccakStateBase::Binary;

        let input: Vec<_> = buffer_if_we_pad.into_iter().map(|el| el.inner).collect();
        let input: [_; 17] = input.try_into().unwrap();

        let state_after_absorb = keccak_gadget.keccak_absorb_into_state_into_binary_base(
            cs,
            current_keccak_state,
            input,
        )?;
        assert!(state_after_absorb.base == KeccakStateBase::First);
        let (new_inner, squeezed) = keccak_gadget
            .keccak_normal_rounds_function_state_in_first_base(cs, state_after_absorb)?;
        assert!(new_inner.base == KeccakStateBase::Binary);

        // keccak_internal_state = new_inner.into_raw();

        let squeezed: Vec<_> = squeezed
            .into_iter()
            .map(|el| UInt64::from_num_unchecked(el))
            .collect();
        let squeezed: [_; 4] = squeezed.try_into().unwrap();

        for (dst, src) in output_words.iter_mut().zip(squeezed.into_iter()) {
            *dst = UInt64::conditionally_select(cs, &output_completed, &*dst, &src)?;
        }

        // we do not need anymore updates as emptiness of input queue is enforced below
    }

    let output_words: Vec<_> = output_words.into_iter().map(|el| el.inner).collect();
    let hash_bytes_if_not_empty =
        crate::scheduler::block_header::keccak_output_into_bytes(cs, output_words)?;
    let hash_bytes_if_not_empty = Bytes32::from_bytes_array(&hash_bytes_if_not_empty);

    let pubdata_hash_as_bytes32 = Bytes32::conditionally_select(
        cs,
        &empty_pubdata,
        &empty_output_hash,
        &hash_bytes_if_not_empty,
    )?;

    initial_queue.enforce_to_be_empty(cs)?;

    assert_eq!(raw_items_bytes.len(), 4 + SERIALIZATION_WIDTH * limit);

    Ok((pubdata_hash_as_bytes32, (num_items, raw_items_bytes)))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::glue::pubdata_hasher::storage_write_data::InitialStorageWriteData;

    #[test]
    fn test_empty_pubdata_hash() -> Result<(), SynthesisError> {
        let (mut tcs, round_function, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut tcs;

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

        let mut input_queue =
            FixedWidthEncodingGenericQueue::<_, InitialStorageWriteData<_>, 3>::empty();
        // trick to prevent constant prop
        input_queue.num_items = UInt32::alloc_from_witness(cs, Some(0))?;
        use sha3::Digest;
        let empty_input_hash = sha3::Keccak256::digest(&[0u8; 4]);
        let mut byte_array = [0u8; 32];
        byte_array.copy_from_slice(empty_input_hash.as_slice());

        let (circuit_hash, _) = hash_pubdata_inner(cs, input_queue, &round_function, 16)?;

        let circuit_hash = circuit_hash.create_witness().unwrap().inner;

        assert_eq!(byte_array, circuit_hash);

        Ok(())
    }

    #[test]
    fn test_very_short_hash() -> Result<(), SynthesisError> {
        // 1 round of keccak required
        let (mut tcs, round_function, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut tcs;

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

        let mut input_queue =
            FixedWidthEncodingGenericQueue::<_, InitialStorageWriteData<_>, 3>::empty();
        let el = InitialStorageWriteData {
            key: Bytes32::constant_from_bytes(&[1u8; 32]).inner,
            value: Bytes32::constant_from_bytes(&[2u8; 32]).inner,
        };

        input_queue.push(cs, &el, &Boolean::Constant(true), &round_function)?;

        use sha3::Digest;
        let mut hasher = sha3::Keccak256::new();
        hasher.update(&1u32.to_be_bytes()); // 1u32 BE
        hasher.update(&[1u8; 32]);
        hasher.update(&[2u8; 32]);

        let output_hash = hasher.finalize();
        let mut byte_array = [0u8; 32];
        byte_array.copy_from_slice(output_hash.as_slice());

        println!("Expecting 0x{}", hex::encode(&byte_array));

        let (circuit_hash, _) = hash_pubdata_inner(cs, input_queue, &round_function, 16)?;

        let circuit_hash = circuit_hash.create_witness().unwrap().inner;

        assert_eq!(byte_array, circuit_hash);

        Ok(())
    }

    #[test]
    fn test_few_rounds_hash() -> Result<(), SynthesisError> {
        // 2 rounds of keccak required
        let (mut tcs, round_function, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut tcs;

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

        let mut input_queue =
            FixedWidthEncodingGenericQueue::<_, InitialStorageWriteData<_>, 3>::empty();
        let el = InitialStorageWriteData {
            key: Bytes32::constant_from_bytes(&[1u8; 32]).inner,
            value: Bytes32::constant_from_bytes(&[2u8; 32]).inner,
        };

        input_queue.push(cs, &el, &Boolean::Constant(true), &round_function)?;

        let el = InitialStorageWriteData {
            key: Bytes32::constant_from_bytes(&[3u8; 32]).inner,
            value: Bytes32::constant_from_bytes(&[4u8; 32]).inner,
        };

        input_queue.push(cs, &el, &Boolean::Constant(true), &round_function)?;

        let el = InitialStorageWriteData {
            key: Bytes32::constant_from_bytes(&[5u8; 32]).inner,
            value: Bytes32::constant_from_bytes(&[6u8; 32]).inner,
        };

        input_queue.push(cs, &el, &Boolean::Constant(true), &round_function)?;

        use sha3::Digest;
        let mut hasher = sha3::Keccak256::new();
        hasher.update(&3u32.to_be_bytes());
        hasher.update(&[1u8; 32]);
        hasher.update(&[2u8; 32]);
        hasher.update(&[3u8; 32]);
        hasher.update(&[4u8; 32]);
        hasher.update(&[5u8; 32]);
        hasher.update(&[6u8; 32]);

        let output_hash = hasher.finalize();
        let mut byte_array = [0u8; 32];
        byte_array.copy_from_slice(output_hash.as_slice());

        println!("Expecting 0x{}", hex::encode(&byte_array));

        let (circuit_hash, _) = hash_pubdata_inner(cs, input_queue, &round_function, 16)?;

        let circuit_hash = circuit_hash.create_witness().unwrap().inner;

        assert_eq!(byte_array, circuit_hash);

        Ok(())
    }

    #[test]
    fn test_use_odd_rounds() -> Result<(), SynthesisError> {
        let (mut tcs, round_function, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut tcs;

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

        let mut input_queue =
            FixedWidthEncodingGenericQueue::<_, InitialStorageWriteData<_>, 3>::empty();

        let bool_true = Boolean::alloc(cs, Some(true))?;
        for _ in 0..3 {
            let el = InitialStorageWriteData {
                key: Bytes32::constant_from_bytes(&[1u8; 32]).inner,
                value: Bytes32::constant_from_bytes(&[2u8; 32]).inner,
            };

            input_queue.push(cs, &el, &bool_true, &round_function)?;
        }

        use sha3::Digest;
        let mut hasher = sha3::Keccak256::new();
        hasher.update(&3u32.to_be_bytes());
        for _ in 0..3 {
            hasher.update(&[1u8; 32]);
            hasher.update(&[2u8; 32]);
        }

        let output_hash = hasher.finalize();
        let mut byte_array = [0u8; 32];
        byte_array.copy_from_slice(output_hash.as_slice());

        println!("Expecting 0x{}", hex::encode(&byte_array));

        let (circuit_hash, _) = hash_pubdata_inner(cs, input_queue, &round_function, 16)?;

        let circuit_hash = circuit_hash.create_witness().unwrap().inner;

        assert_eq!(byte_array, circuit_hash);

        Ok(())
    }

    #[test]
    fn test_use_all_rounds() -> Result<(), SynthesisError> {
        let (mut tcs, round_function, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut tcs;

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

        let mut input_queue =
            FixedWidthEncodingGenericQueue::<_, InitialStorageWriteData<_>, 3>::empty();

        let bool_true = Boolean::alloc(cs, Some(true))?;
        for _ in 0..16 {
            let el = InitialStorageWriteData {
                key: Bytes32::constant_from_bytes(&[1u8; 32]).inner,
                value: Bytes32::constant_from_bytes(&[2u8; 32]).inner,
            };

            input_queue.push(cs, &el, &bool_true, &round_function)?;
        }

        use sha3::Digest;
        let mut hasher = sha3::Keccak256::new();
        hasher.update(&16u32.to_be_bytes());
        for _ in 0..16 {
            hasher.update(&[1u8; 32]);
            hasher.update(&[2u8; 32]);
        }

        let output_hash = hasher.finalize();
        let mut byte_array = [0u8; 32];
        byte_array.copy_from_slice(output_hash.as_slice());

        println!("Expecting 0x{}", hex::encode(&byte_array));

        let (circuit_hash, _) = hash_pubdata_inner(cs, input_queue, &round_function, 16)?;

        let circuit_hash = circuit_hash.create_witness().unwrap().inner;

        assert_eq!(byte_array, circuit_hash);

        Ok(())
    }
}
