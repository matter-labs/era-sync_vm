use super::*;

pub mod input;
pub mod storage_write_data;
pub mod variable_length;

use crate::glue::optimizable_queue::FixedWidthEncodingGenericQueue;
use crate::glue::pubdata_hasher::storage_write_data::ByteSerializable;

use self::input::*;

pub fn hash_pubdata_entry_point<
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

    use crate::glue::binary_hashes::CircuitBinaryHasher;
    use crate::glue::binary_hashes::Keccak256Hasher;
    let hasher = Keccak256Hasher::new(cs)?;

    let num_items = initial_queue.len();
    let num_items_bytes = num_items.into_be_bytes(cs)?;
    assert_eq!(num_items_bytes.len(), 4);

    let mut hash_input = num_items_bytes;
    hash_input.resize(4 + (limit * SERIALIZATION_WIDTH), Byte::zero());

    for chunk in hash_input[4..].chunks_exact_mut(SERIALIZATION_WIDTH) {
        let can_pop = initial_queue.is_empty(cs)?.not();
        let item = initial_queue.pop_first(cs, &can_pop, round_function)?;
        let serialized = item.serialize(cs)?;
        assert_eq!(chunk.len(), serialized.len());
        for (dst, src) in chunk.iter_mut().zip(serialized.iter()) {
            *dst = Byte::conditionally_select(cs, &can_pop, src, dst)?;
        }
    }

    initial_queue.enforce_to_be_empty(cs)?;

    let pubdata_hash = hasher.hash(cs, &hash_input)?;
    let pubdata_hash_as_bytes32 = Bytes32::from_bytes_array(&pubdata_hash);

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
