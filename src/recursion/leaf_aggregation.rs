use super::*;
use crate::glue::traits::get_vec_witness_raw;
use crate::vm::structural_eq::*;
use cs_derive::*;

use crate::recursion::recursion_tree::NUM_LIMBS;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;
use crate::vm::primitives::*;

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
pub struct LeafAggregationInputData<E: Engine> {
    pub leaf_vk_committment: Num<E>,
    pub initial_log_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for LeafAggregationInputData<E> {
    fn empty() -> Self {
        Self {
            leaf_vk_committment: Num::zero(),
            initial_log_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
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
pub struct LeafAggregationOutputData<E: Engine> {
    pub pair_with_x_x: [Num<E>; NUM_LIMBS],
    pub pair_with_x_y: [Num<E>; NUM_LIMBS],
    pub pair_with_generator_x: [Num<E>; NUM_LIMBS],
    pub pair_with_generator_y: [Num<E>; NUM_LIMBS],
}

impl<E: Engine> CircuitEmpty<E> for LeafAggregationOutputData<E> {
    fn empty() -> Self {
        Self {
            pair_with_x_x: [Num::zero(); NUM_LIMBS],
            pair_with_x_y: [Num::zero(); NUM_LIMBS],
            pair_with_generator_x: [Num::zero(); NUM_LIMBS],
            pair_with_generator_y: [Num::zero(); NUM_LIMBS],
        }
    }
}

pub type LeafAggregationInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    (),
    LeafAggregationInputData<E>,
    LeafAggregationOutputData<E>,
>;
pub type LeafAggregationInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    (),
    LeafAggregationInputData<E>,
    LeafAggregationOutputData<E>,
>;

use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;
use crate::scheduler::RecursiveProofQuery;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct LeafAggregationCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: LeafAggregationInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<RecursiveProofQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<RecursiveProofQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub initial_queue_witness: FixedWidthEncodingGenericQueueWitness<E, RecursiveProofQuery<E>, 2>,

    pub leaf_vks_committments_set: Vec<E::Fr>,
    #[derivative(Debug = "ignore")]
    pub proof_witnesses: Vec<ZkSyncParametricProof<E>>,

    pub vk_encoding_witnesses: Vec<Vec<E::Fr>>,
}

use crate::project_ref;
use crate::recursion::node_aggregation::ZkSyncParametricProof;
use crate::recursion::node_aggregation::VK_ENCODING_LENGTH;
use crate::recursion::recursion_tree::AggregationParameters;
use crate::scheduler::RecursiveProofQueue;
use franklin_crypto::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;

pub fn aggregate_at_leaf_level_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    T: TranscriptGadget<E>,
    P: HashParams<E, 2, 3>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const USE_MODIFIED_MAIN_GATE: bool,
>(
    cs: &mut CS,
    witness: Option<LeafAggregationCircuitInstanceWitness<E>>,
    round_function: &R,
    params: (
        usize,
        RnsParameters<E, E::Fq>,
        AggregationParameters<E, T, P, 2, 3>,
        E::Fr,
        [E::Fr; VK_ENCODING_LENGTH],
        Vec<E::Fr>,
        Vec<ZkSyncParametricProof<E>>,
        Option<[E::G2Affine; 2]>,
    ),
) -> Result<(AllocatedNum<E>, LeafAggregationOutputData<E>), SynthesisError> {
    let (
        num_proofs_to_aggregate,
        rns_params,
        aggregation_params,
        padding_vk_committment,
        padding_vk_encoding,
        padding_public_inputs,
        padding_proofs,
        g2_elements,
    ) = params;

    assert_eq!(num_proofs_to_aggregate, padding_public_inputs.len());
    assert_eq!(num_proofs_to_aggregate, padding_proofs.len());

    inscribe_default_range_table_for_bit_width_over_first_three_columns(
        cs,
        RANGE_CHECK_TABLE_BIT_WIDTH,
    )?;

    let structured_input = project_ref!(witness, closed_form_input).cloned();
    let mut structured_input =
        LeafAggregationInputOutput::alloc_ignoring_outputs(cs, structured_input)?;

    let mut recursion_requests_queue = RecursiveProofQueue::from_state(
        cs,
        structured_input.observable_input.initial_log_queue_state,
    )?;
    if let Some(wit) = project_ref!(witness, initial_queue_witness).cloned() {
        recursion_requests_queue.witness = wit;
    }

    let mut key_committments = vec![];
    let mut inputs = vec![];

    let mut leaf_vks_committments_set = project_ref!(witness, leaf_vks_committments_set).cloned();

    use crate::scheduler::CircuitType;

    let sequence_of_circuit_types = [
        CircuitType::VM,
        CircuitType::DecommitmentsFilter,
        CircuitType::Decommiter,
        CircuitType::LogDemultiplexer,
        CircuitType::KeccakPrecompile,
        CircuitType::Sha256Precompile,
        CircuitType::EcrecoverPrecompile,
        CircuitType::RamValidation,
        CircuitType::StorageFilter,
        CircuitType::StorageApplicator,
        CircuitType::StorageFreshWritesHasher,
        CircuitType::StorageRepeatedWritesHasher,
        CircuitType::EventsRevertsFilter,
        CircuitType::L1MessagesRevertsFilter,
        CircuitType::L1MessagesHasher,
        CircuitType::L1MessagesMerkelization,
    ];

    let mut vk_committments = vec![];

    for el in sequence_of_circuit_types.iter() {
        let wit = get_vec_witness_raw(&mut leaf_vks_committments_set, E::Fr::zero());
        let circuit_type = UInt8::from_uint(*el as u8);
        let vk = Num::alloc(cs, wit)?;
        vk_committments.push((circuit_type, vk));
    }

    let mut aggregation_proofs = project_ref!(witness, proof_witnesses).cloned();
    let mut vks_raw_elements_witness = project_ref!(witness, vk_encoding_witnesses).map(|el| {
        let mut result = vec![];
        for subset in el.iter().cloned() {
            let r = subset.try_into().unwrap();
            result.push(r);
        }

        result
    });

    for proof_idx in 0..num_proofs_to_aggregate {
        let is_empty = recursion_requests_queue.is_empty(cs)?;
        let pop_for_leaf = is_empty.not();
        let do_padding = is_empty;

        let leaf_request = recursion_requests_queue.pop_first(cs, &pop_for_leaf, round_function)?;
        // dbg!(&leaf_request.create_witness());

        let mut input_to_use = Num::Constant(padding_public_inputs[proof_idx]);
        let mut vk_committment_to_use = Num::Constant(padding_vk_committment);

        if do_padding.get_value().unwrap_or(false) {
            if let Some(dst) = aggregation_proofs.as_mut() {
                dst.push(padding_proofs[proof_idx].clone());
            }

            if let Some(dst) = vks_raw_elements_witness.as_mut() {
                dst.push(padding_vk_encoding);
            }
        }

        let mut flags = vec![];

        use crate::vm::partitioner::*;

        for (circuit_type, vk_committment) in vk_committments.iter() {
            let matches = UInt8::equals(cs, circuit_type, &leaf_request.cicruit_type)?;
            flags.push(matches);
            let should_use = smart_and(cs, &[matches, pop_for_leaf])?;

            vk_committment_to_use = Num::conditionally_select(
                cs,
                &should_use,
                &vk_committment,
                &vk_committment_to_use,
            )?;
            input_to_use = Num::conditionally_select(
                cs,
                &should_use,
                &leaf_request.closed_form_input_hash,
                &input_to_use,
            )?;
        }

        let used_some_of_those = smart_or(cs, &flags)?;
        can_not_be_false_if_flagged(cs, &used_some_of_those, &pop_for_leaf)?;

        key_committments.push(vk_committment_to_use);
        inputs.push(input_to_use);
    }

    assert_eq!(key_committments.len(), inputs.len());
    assert_eq!(key_committments.len(), num_proofs_to_aggregate);

    use crate::recursion::node_aggregation::aggregate_generic_inner;

    // do actual work
    let [[pair_with_generator_x, pair_with_generator_y], [pair_with_x_x, pair_with_x_y]] =
        aggregate_generic_inner::<_, _, _, _, _, _, true>(
            cs,
            key_committments,
            inputs,
            aggregation_proofs,
            aggregation_params,
            &rns_params,
            padding_proofs[0].clone(), // actually unused
            None,                      // no results to aggregate on top
            round_function,
            vks_raw_elements_witness,
            padding_vk_encoding,
            g2_elements,
            num_proofs_to_aggregate,
        )?;

    let self_output = LeafAggregationOutputData {
        pair_with_x_x,
        pair_with_x_y,
        pair_with_generator_x,
        pair_with_generator_y,
    };

    structured_input.start_flag = Boolean::constant(true);
    structured_input.completion_flag = Boolean::constant(true);
    structured_input.observable_output = self_output.clone();

    use crate::inputs::ClosedFormInputCompactForm;
    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    // dbg!(compact_form.create_witness());
    use crate::glue::optimizable_queue::commit_encodable_item;

    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();
    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;

    Ok((public_input, self_output))
}
