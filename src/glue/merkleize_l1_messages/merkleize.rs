use super::tree_hasher::CircuitTreeHasher;
use super::*;
use crate::vm::primitives::small_uints::{UInt32, UInt64};
use crate::{
    circuit_structures::{
        byte::{Byte, IntoBytes},
        traits::CircuitArithmeticRoundFunction,
        utils::can_not_be_false_if_flagged,
    },
    franklin_crypto::{
        bellman::{plonk::better_better_cs::cs::ConstraintSystem, Engine, Field, SynthesisError},
        plonk::circuit::{allocated_num::Num, boolean::Boolean},
    },
    glue::optimizable_queue::{
        commit_encodable_item, FixedWidthEncodingGenericQueue,
        FixedWidthEncodingGenericQueueWitness,
    },
    utils::{compute_shifts, log2_floor},
    vm::{optimizer::sponge_set::SpongeOptimizer, primitives::uint256::UInt256},
};
use cs_derive::*;
use franklin_crypto::plonk::circuit::{
    byte::{uniquely_encode_be_bytes, uniquely_encode_le_bytes_into_num},
    linear_combination::LinearCombination,
};
use std::convert::TryInto;

use crate::glue::traits::*;
use crate::vm::partitioner::*;
use crate::vm::structural_eq::*;
use derivative::*;
use num_bigint::BigUint;
use num_traits::Zero;

use super::input::*;

pub fn merklize_messages_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    H: CircuitTreeHasher<E>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const ARITY: usize,
>(
    cs: &mut CS,
    witness: Option<
        MessagesMerklizerInstanceWitness<
            E,
            STORAGE_LOG_RECORD_ENCODING_LEN,
            MESSAGE_SERIALIZATION_BYTES,
            StorageLogRecord<E>,
        >,
    >,
    round_function: &R,
    config: (usize, bool),
) -> Result<AllocatedNum<E>, SynthesisError> {
    let (limit, output_linear_hash) = config;

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

    assert!(
        is_power_of_n(limit, ARITY),
        "limit should be a power of two"
    );

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let input_queue_witness = project_ref!(witness, input_queue_witness).cloned();

    let mut structured_input =
        MessagesMerklizerInputOutput::alloc_ignoring_outputs(cs, structured_input_witness.clone())?;

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

    if let Some(len) = initial_queue.len().get_value() {
        assert!(len <= limit as u32, "queue contains items more than limit");
    }

    let tree_hasher = H::new(cs)?;

    let (calculated_merkle_root_bytes, linear_hash) =
        merkleize_l1_messages_inner::<_, _, _, _, AWIDTH, SWIDTH, ARITY>(
            cs,
            initial_queue,
            round_function,
            &tree_hasher,
            limit,
            output_linear_hash,
        )?;

    // form the final state
    structured_input.observable_output = MessagesMerklizerOutputData::empty();
    structured_input.observable_output.linear_hash = linear_hash;
    structured_input.observable_output.root_hash = calculated_merkle_root_bytes;

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

pub(crate) fn le_bytes_into_uint256<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bytes: [Byte<E>; 32],
) -> Result<UInt256<E>, SynthesisError> {
    let shifts = compute_shifts::<E::Fr>();

    let mut limbs = [UInt64::zero(); 4];
    for (limb, byte_chunk) in limbs.iter_mut().zip(bytes.chunks_exact(8)) {
        let mut lc = LinearCombination::zero();
        for (i, byte) in byte_chunk.iter().enumerate() {
            lc.add_assign_number_with_coeff(&byte.inner, shifts[i * 8]);
        }
        *limb = UInt64::from_num_unchecked(lc.into_num(cs)?);
    }

    Ok(UInt256 { inner: limbs })
}

pub(crate) fn merkleize_l1_messages_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    H: CircuitTreeHasher<E>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const ARITY: usize,
>(
    cs: &mut CS,
    mut initial_queue: StorageLogQueue<E>,
    round_function: &R,
    tree_hasher: &H,
    limit: usize,
    output_linear_hash: bool,
) -> Result<(Bytes32<E>, Bytes32<E>), SynthesisError> {
    let num_items = initial_queue.len();
    let num_items_bytes = num_items.into_be_bytes(cs)?;
    assert_eq!(num_items_bytes.len(), 4);

    let mut linear_hash_input = num_items_bytes;
    linear_hash_input.resize(4 + (limit * MESSAGE_SERIALIZATION_BYTES), Byte::zero());

    use crate::glue::pubdata_hasher::storage_write_data::ByteSerializable;

    for chunk in linear_hash_input[4..].chunks_exact_mut(MESSAGE_SERIALIZATION_BYTES) {
        let can_pop = initial_queue.is_empty(cs)?.not();
        let item = initial_queue.pop_first(cs, &can_pop, round_function)?;
        let serialized = item.serialize(cs)?;
        assert_eq!(chunk.len(), serialized.len());
        for (dst, src) in chunk.iter_mut().zip(serialized.iter()) {
            *dst = Byte::conditionally_select(cs, &can_pop, src, dst)?;
        }
    }

    let linear_hash = if output_linear_hash {
        println!(
            "Computing linear hash over {} bytes",
            linear_hash_input.len()
        );
        let pubdata_hash = tree_hasher.hash(cs, &linear_hash_input)?;
        let pubdata_hash_as_bytes32 = Bytes32::from_bytes_array(&pubdata_hash);

        pubdata_hash_as_bytes32
    } else {
        Bytes32::empty()
    };

    // a little bit tricky: unsafe cast, but we checked the length, and ABI wise it's guaranteed
    // later on we can use split_array_ref

    let leafs_only_bytes = &linear_hash_input[4..];
    assert!(leafs_only_bytes.len() % MESSAGE_SERIALIZATION_BYTES == 0);

    let mut leafs = vec![];
    for chunk in leafs_only_bytes.chunks_exact(MESSAGE_SERIALIZATION_BYTES) {
        let leaf_encoding: [_; MESSAGE_SERIALIZATION_BYTES] = chunk.to_vec().try_into().unwrap();
        leafs.push(leaf_encoding);
    }

    println!("Computing tree over {} leafs", leafs.len());

    let calculated_merkle_root =
        circuit_compute_merkle_root_from_leafs_generic::<_, _, H, ARITY>(cs, &leafs, tree_hasher)?;

    initial_queue.enforce_to_be_empty(cs)?;

    Ok((
        Bytes32::from_bytes_array(&calculated_merkle_root),
        linear_hash,
    ))
}

pub fn merklize_messages_variable_length_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    H: CircuitTreeHasher<E>,
    const ARITY: usize,
>(
    cs: &mut CS,
    witness: Option<
        MessagesMerklizerInstanceWitness<
            E,
            STORAGE_LOG_RECORD_ENCODING_LEN,
            MESSAGE_SERIALIZATION_BYTES,
            StorageLogRecord<E>,
        >,
    >,
    round_function: &R,
    config: (usize, bool),
) -> Result<AllocatedNum<E>, SynthesisError> {
    let (limit, output_linear_hash) = config;

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

    assert!(
        is_power_of_n(limit, ARITY),
        "limit should be a power of arity {}",
        ARITY
    );

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let input_queue_witness = project_ref!(witness, input_queue_witness).cloned();

    let mut structured_input =
        MessagesMerklizerInputOutput::alloc_ignoring_outputs(cs, structured_input_witness.clone())?;

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

    if let Some(len) = initial_queue.len().get_value() {
        assert!(len <= limit as u32, "queue contains items more than limit");
    }

    let tree_hasher = H::new(cs)?;

    let (calculated_merkle_root_bytes, linear_hash) =
        merkleize_l1_messages_inner_variable_length::<_, _, _, _, ARITY>(
            cs,
            initial_queue,
            round_function,
            &tree_hasher,
            limit,
            output_linear_hash,
        )?;

    // form the final state
    structured_input.observable_output = MessagesMerklizerOutputData::empty();
    structured_input.observable_output.linear_hash = linear_hash;
    structured_input.observable_output.root_hash = calculated_merkle_root_bytes;

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

pub(crate) fn merkleize_l1_messages_inner_variable_length<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    H: CircuitTreeHasher<E>,
    const ARITY: usize,
>(
    cs: &mut CS,
    mut initial_queue: StorageLogQueue<E>,
    round_function: &R,
    tree_hasher: &H,
    limit: usize,
    output_linear_hash: bool,
) -> Result<(Bytes32<E>, Bytes32<E>), SynthesisError> {
    println!("{}", output_linear_hash);

    let (linear_hash, linear_hash_input) = if output_linear_hash {
        use crate::glue::pubdata_hasher::variable_length::hash_pubdata_inner;

        let (linear_hash, (_num_items, raw_bytes)) =
            hash_pubdata_inner(cs, initial_queue, round_function, limit)?;

        (linear_hash, raw_bytes)
    } else {
        let num_items = initial_queue.len();
        let num_items_bytes = num_items.into_be_bytes(cs)?;
        assert_eq!(num_items_bytes.len(), 4);

        let mut linear_hash_input = num_items_bytes;
        linear_hash_input.resize(4 + (limit * MESSAGE_SERIALIZATION_BYTES), Byte::zero());

        use crate::glue::pubdata_hasher::storage_write_data::ByteSerializable;

        for chunk in linear_hash_input[4..].chunks_exact_mut(MESSAGE_SERIALIZATION_BYTES) {
            let can_pop = initial_queue.is_empty(cs)?.not();
            let item = initial_queue.pop_first(cs, &can_pop, round_function)?;
            let serialized = item.serialize(cs)?;
            assert_eq!(chunk.len(), serialized.len());
            for (dst, src) in chunk.iter_mut().zip(serialized.iter()) {
                *dst = Byte::conditionally_select(cs, &can_pop, src, dst)?;
            }
        }

        initial_queue.enforce_to_be_empty(cs)?;

        (Bytes32::empty(), linear_hash_input)
    };

    let leafs_only_bytes = &linear_hash_input[4..];
    assert!(
        leafs_only_bytes.len() % MESSAGE_SERIALIZATION_BYTES == 0,
        "serialization of leafs is {} bytes long and not divisible by {}",
        leafs_only_bytes.len(),
        MESSAGE_SERIALIZATION_BYTES
    );

    let mut leafs = vec![];
    for chunk in leafs_only_bytes.chunks_exact(MESSAGE_SERIALIZATION_BYTES) {
        let leaf_encoding: [_; MESSAGE_SERIALIZATION_BYTES] = chunk.to_vec().try_into().unwrap();
        leafs.push(leaf_encoding);
    }

    println!("Computing tree over {} leafs", leafs.len());

    let calculated_merkle_root =
        circuit_compute_merkle_root_from_leafs_generic::<_, _, H, ARITY>(cs, &leafs, tree_hasher)?;

    Ok((
        Bytes32::from_bytes_array(&calculated_merkle_root),
        linear_hash,
    ))
}

fn circuit_compute_merkle_root_from_leafs_generic<
    E: Engine,
    CS: ConstraintSystem<E>,
    H: CircuitTreeHasher<E>,
    const ARITY: usize,
>(
    cs: &mut CS,
    leafs: &[[Byte<E>; MESSAGE_SERIALIZATION_BYTES]],
    tree_hasher: &H,
) -> Result<[Byte<E>; 32], SynthesisError> {
    let num_leafs = leafs.len();

    assert!(
        is_power_of_n(num_leafs, ARITY),
        "number of leafs must be a power of {}",
        ARITY
    );

    let depth = if ARITY == 2 {
        log2_floor(num_leafs) as usize
    } else if ARITY == 4 {
        (log2_floor(num_leafs) / 2) as usize
    } else {
        unimplemented!("only 4ary or 2ary are allowed")
    };

    let mut leaf_hashes = Vec::with_capacity(leafs.len());

    for el in leafs.iter() {
        let leaf_hash = tree_hasher.leaf_hash(cs, el)?;
        leaf_hashes.push(leaf_hash);
    }

    let mut previous_layer_hashes = leaf_hashes;
    let mut node_hashes = vec![];

    for _level in 0..depth {
        assert!(previous_layer_hashes.len() % ARITY == 0);
        for pair in previous_layer_hashes.chunks(ARITY) {
            let nodes: [_; ARITY] = pair.try_into().unwrap();
            let new_node_hash = tree_hasher.node_hash(cs, &nodes)?;
            node_hashes.push(new_node_hash);
        }

        let p = std::mem::replace(&mut node_hashes, vec![]);
        previous_layer_hashes = p;
    }

    assert_eq!(previous_layer_hashes.len(), 1);
    let root = previous_layer_hashes[0];

    Ok(root)

    // // (a^(d+1) - 1) / (d-1)
    // let all_nodes_length = (ARITY.pow(depth as u32 + 1) - 1) / (ARITY - 1);

    // let mut all_nodes = vec![[Byte::zero(); 32]; all_nodes_length];
    // for (idx, leaf_values) in leafs.iter().enumerate() {
    //     all_nodes[idx] = tree_hasher.leaf_hash(cs, leaf_values)?;
    // }

    // let mut nodes_ref = &mut all_nodes[..];
    // let mut split_at = num_leafs;

    // for _ in 0..depth {
    //     let (this_level, next_level) = nodes_ref.split_at_mut(split_at);
    //     split_at /= ARITY;
    //     let (output, _) = next_level.split_at_mut(split_at);

    //     for (out, inp) in output.iter_mut().zip(this_level.chunks_exact(ARITY)) {
    //         *out = tree_hasher.node_hash::<_, ARITY>(cs, inp.try_into().expect("length match"))?;
    //     }

    //     nodes_ref = next_level;
    // }

    // let root_idx = all_nodes.len() - 1;

    // Ok(all_nodes[root_idx])
}

pub(crate) fn is_power_of_n(number: usize, base: usize) -> bool {
    let mut number = number;

    if number == 0 {
        return false;
    }

    while number != 1 {
        if number % base != 0 {
            return false;
        }
        number /= base
    }

    true
}

use crate::glue::binary_hashes::CircuitBinaryHasher;

pub(crate) fn byte_encodable_queue_binary_hash<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitSelectable<E>
        + CircuitFixedLengthEncodableExt<E, N>
        + CircuitFixedLengthDecodableExt<E, N>
        + IntoBytes<E>
        + CircuitEmpty<E>,
    B: CircuitBinaryHasher<E>,
    const N: usize,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    mut queue: FixedWidthEncodingGenericQueue<E, I, N>,
    round_function: &R,
    binary_hasher: &B,
    include_length: bool,
    encode_be: bool,
    limit: usize,
) -> Result<[Byte<E>; 32], SynthesisError> {
    if let Some(len) = queue.len().get_value() {
        assert!(len <= limit as u32, "queue contains items more than limit");
    }

    let mut bytes = if include_length {
        vec![Byte::empty(); 4 + limit * I::encoding_len()]
    } else {
        vec![Byte::empty(); limit * I::encoding_len()]
    };

    if include_length {
        let length = queue.len();
        let length_encoding = num_into_bytes_be(cs, length.inner, 32)?;
        bytes[0..4].copy_from_slice(&length_encoding);
    }

    let encoding_area = if include_length {
        &mut bytes[4..]
    } else {
        &mut bytes[..]
    };

    // this one is guaranteed to encode to all zeroes;
    let empty_value = I::empty();
    for (_, chunk) in (0..limit).zip(encoding_area.chunks_exact_mut(I::encoding_len())) {
        let is_empty = queue.is_empty(cs)?;

        let current_item = queue.pop_first(cs, &is_empty.not(), round_function)?;
        let current_item = I::conditionally_select(cs, &is_empty, &empty_value, &current_item)?;

        let encoding = if encode_be {
            current_item.into_be_bytes(cs)?
        } else {
            current_item.into_le_bytes(cs)?
        };

        chunk.copy_from_slice(&encoding);
    }

    drop(encoding_area);

    let binary_hash = binary_hasher.hash(cs, &bytes)?;

    Ok(binary_hash)
}
