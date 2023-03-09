use super::*;
use crate::project_ref;
use crate::vm::structural_eq::*;
use cs_derive::*;
use franklin_crypto::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;

use crate::recursion::recursion_tree::NUM_LIMBS;

use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;

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
pub struct NodeAggregationInputData<E: Engine> {
    pub node_vk_committment: Num<E>, // vk for node level aggregator
    pub leaf_vk_committment: Num<E>, // vk for leaf level aggregator
    pub all_circuit_types_committment_for_leaf: Num<E>, // idividual keys set used by leaf
    pub initial_log_queue_state: FixedWidthEncodingGenericQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for NodeAggregationInputData<E> {
    fn empty() -> Self {
        Self {
            node_vk_committment: Num::zero(),
            leaf_vk_committment: Num::zero(),
            all_circuit_types_committment_for_leaf: Num::zero(),
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
pub struct NodeAggregationOutputData<E: Engine> {
    pub pair_with_x_x: [Num<E>; NUM_LIMBS],
    pub pair_with_x_y: [Num<E>; NUM_LIMBS],
    pub pair_with_generator_x: [Num<E>; NUM_LIMBS],
    pub pair_with_generator_y: [Num<E>; NUM_LIMBS],
}

impl<E: Engine> CircuitEmpty<E> for NodeAggregationOutputData<E> {
    fn empty() -> Self {
        Self {
            pair_with_x_x: [Num::zero(); NUM_LIMBS],
            pair_with_x_y: [Num::zero(); NUM_LIMBS],
            pair_with_generator_x: [Num::zero(); NUM_LIMBS],
            pair_with_generator_y: [Num::zero(); NUM_LIMBS],
        }
    }
}

pub type NodeAggregationInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    (),
    NodeAggregationInputData<E>,
    NodeAggregationOutputData<E>,
>;
pub type NodeAggregationInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    (),
    NodeAggregationInputData<E>,
    NodeAggregationOutputData<E>,
>;

use crate::bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;
use crate::recursion::leaf_aggregation::*;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;
use crate::scheduler::RecursiveProofQuery;

pub type ZkSyncParametricCircuit<E> = MainGateParametrizedCircuitWithNonlinearityAndLookups<
    E,
    SelectorOptimizedWidth4MainGateWithDNext,
>;
pub type ZkSyncParametricProof<E> = Proof<E, ZkSyncParametricCircuit<E>>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct NodeAggregationCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: NodeAggregationInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<RecursiveProofQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<RecursiveProofQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub initial_queue_witness: FixedWidthEncodingGenericQueueWitness<E, RecursiveProofQuery<E>, 2>,

    pub leaf_aggregation_results: Vec<LeafAggregationOutputDataWitness<E>>,
    pub node_aggregation_results: Vec<NodeAggregationOutputDataWitness<E>>,
    #[derivative(Debug = "ignore")]
    pub proof_witnesses: Vec<ZkSyncParametricProof<E>>,
    pub depth: u32,
    pub vk_encoding_witnesses: Vec<Vec<E::Fr>>,
}

pub const VK_ENCODING_LENGTH: usize = 165;

use crate::vm::partitioner::*;
use crate::vm::primitives::*;

pub fn aggregate_at_node_level_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    T: TranscriptGadget<E>,
    P: HashParams<E, 2, 3>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const USE_MODIFIED_MAIN_GATE: bool,
>(
    cs: &mut CS,
    witness: Option<NodeAggregationCircuitInstanceWitness<E>>,
    round_function: &R,
    params: (
        usize,
        usize,
        RnsParameters<E, E::Fq>,
        AggregationParameters<E, T, P, 2, 3>,
        E::Fr,
        [E::Fr; VK_ENCODING_LENGTH],
        Vec<E::Fr>,
        Vec<ZkSyncParametricProof<E>>,
        Vec<(
            [E::Fr; NUM_LIMBS],
            [E::Fr; NUM_LIMBS],
            [E::Fr; NUM_LIMBS],
            [E::Fr; NUM_LIMBS],
        )>,
        Option<[E::G2Affine; 2]>,
    ),
) -> Result<
    (
        AllocatedNum<E>,
        Vec<LeafAggregationInputOutput<E>>,
        Vec<NodeAggregationInputOutput<E>>,
        NodeAggregationOutputData<E>,
    ),
    SynthesisError,
> {
    let (
        num_proofs_to_aggregate,
        num_proofs_aggregated_by_leaf,
        rns_params,
        aggregation_params,
        padding_vk_committment,
        padding_vk_encoding,
        padding_public_inputs,
        padding_proofs,
        padding_aggregation_sets,
        // (padding_pair_with_gen_x, padding_pair_with_gen_y, padding_pair_with_x_x, padding_pair_with_x_y),
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
        NodeAggregationInputOutput::alloc_ignoring_outputs(cs, structured_input)?;

    let mut recursion_requests_queue = RecursiveProofQueue::from_state(
        cs,
        structured_input.observable_input.initial_log_queue_state,
    )?;
    if let Some(wit) = project_ref!(witness, initial_queue_witness).cloned() {
        recursion_requests_queue.witness = wit;
    }

    // our circuit should be variable, so it can either aggregate leafs (that themselves aggregate basic circuits and pop from queue),
    // or nodes (that only split the queue)

    // In general we can implement assymmetric tree aggregation, but for now we do simpler plain one, so
    // we can have a half of the tree that effectively aggregate 1 basic circuit

    let depth = project_ref!(witness, depth).cloned();
    let depth = UInt32::alloc_from_witness(cs, depth)?;

    let max_length_to_aggregate_leafs =
        UInt32::from_uint((num_proofs_to_aggregate * num_proofs_aggregated_by_leaf) as u32);
    // max aggregated by splitting into leafs >= total length
    let (_, uf) = max_length_to_aggregate_leafs.sub(cs, &recursion_requests_queue.num_items)?;
    let can_use_leafs = uf.not();

    let should_aggregate_leafs = depth.is_zero(cs)?;

    // if we decide to use leaf strategy then we should be able to aggregate fast enough
    can_not_be_false_if_flagged(cs, &can_use_leafs, &should_aggregate_leafs)?;

    // if we assume that we do not use leafs then we should split by as much as we can (kind of "left affinity").
    // We split into `num_proofs_to_aggregate` pieces, with last piece potentially having less items than other

    const MAX_DEPTH: usize = 6;
    let mut chunk_size = UInt32::from_uint(num_proofs_aggregated_by_leaf as u32);
    let multiplier = UInt32::from_uint((num_proofs_to_aggregate) as u32);
    let mut depth = depth;
    // simple exponentiation
    for _ in 0..MAX_DEPTH {
        let depth_is_zero = depth.is_zero(cs)?;
        depth = depth.conditionally_decrement_unchecked(cs, &depth_is_zero.not())?;
        let next_chunk_size =
            UInt32::from_num_unchecked(chunk_size.inner.mul(cs, &multiplier.inner)?);

        chunk_size =
            UInt32::conditionally_select(cs, &depth_is_zero.not(), &next_chunk_size, &chunk_size)?;
    }

    // assert that depth was "sane". We do not propagage the depth along the proofs since it's not necessary for
    // proof of knowledge: top level scheduler will verify the proof for SOME depth, but that will have a full queue as the input
    // In this case it's depth must be somewhat sufficient
    let depth_is_zero = depth.is_zero(cs)?;
    Boolean::enforce_equal(cs, &depth_is_zero, &Boolean::Constant(true))?;

    let mut leaf_aggregation_results_witnesses =
        project_ref!(witness, leaf_aggregation_results).cloned();
    let mut node_aggregation_results_witnesses =
        project_ref!(witness, node_aggregation_results).cloned();

    let mut casted_aggregation_results = vec![];

    let mut for_leafs = vec![];
    let mut for_nodes = vec![];

    let mut key_committments = vec![];
    let mut inputs = vec![];

    let mut aggregation_proofs = project_ref!(witness, proof_witnesses).cloned();

    // dbg!(aggregation_proofs.as_ref().map(|el| el[0].inputs[0]));

    let mut vks_raw_elements_witness = project_ref!(witness, vk_encoding_witnesses).map(|el| {
        let mut result = vec![];
        for subset in el.iter().cloned() {
            let r = subset.try_into().unwrap();
            result.push(r);
        }

        result
    });

    // if we aggregate leafs then each chunk should take up to `num_proofs_aggregated_by_leaf` (or less),
    // otherwise it should be a size that we have just computed based on depth and how many we can aggregate by
    // leaf and leafs by node
    // e.g
    // depth 0: split_by = num_proofs_aggregated_by_leaf,
    // depth 1: split_by = num_proofs_aggregated_by_leaf * num_proofs_to_aggregate
    // depth 1: split_by = num_proofs_aggregated_by_leaf * num_proofs_to_aggregate * num_proofs_to_aggregate
    // etc

    let split_by = UInt32::conditionally_select(
        cs,
        &should_aggregate_leafs,
        &UInt32::from_uint(num_proofs_aggregated_by_leaf as u32),
        &chunk_size,
    )?;

    // dbg!(split_by.get_value());

    for proof_idx in 0..num_proofs_to_aggregate {
        // dbg!(recursion_requests_queue.num_items.get_value());
        let is_empty = recursion_requests_queue.is_empty(cs)?;
        let use_for_leaf = smart_and(cs, &[is_empty.not(), should_aggregate_leafs])?;
        let use_for_node = smart_and(cs, &[is_empty.not(), should_aggregate_leafs.not()])?;
        let do_padding = is_empty;

        // dbg!(&use_for_leaf.get_value());
        // dbg!(&use_for_node.get_value());
        // dbg!(&do_padding.get_value());

        if do_padding.get_value().unwrap_or(false) {
            if let Some(dst) = aggregation_proofs.as_mut() {
                dst.push(padding_proofs[proof_idx].clone());
            }

            if let Some(dst) = vks_raw_elements_witness.as_mut() {
                dst.push(padding_vk_encoding);
            }
        }

        let (chunk, rest) = recursion_requests_queue.split(cs, split_by)?;
        recursion_requests_queue = rest;

        let chunk_state = chunk.into_state();

        // leaf case

        let input_for_leaf = LeafAggregationInputData {
            leaf_vk_committment: structured_input
                .observable_input
                .all_circuit_types_committment_for_leaf,
            initial_log_queue_state: chunk_state.clone(),
        };

        let output_for_leaf_witness = if use_for_leaf.get_value().unwrap_or(false) {
            get_vec_witness_raw(
                &mut leaf_aggregation_results_witnesses,
                LeafAggregationOutputData::placeholder_witness(),
            )
        } else {
            Some(LeafAggregationOutputData::placeholder_witness())
        };

        let output_for_leaf =
            LeafAggregationOutputData::alloc_from_witness(cs, output_for_leaf_witness)?;

        let leaf_closed_form_input = LeafAggregationInputOutput {
            start_flag: Boolean::constant(true),
            completion_flag: Boolean::constant(true), // those do not matter
            observable_input: input_for_leaf,
            observable_output: output_for_leaf.clone(),
            hidden_fsm_input: (),
            hidden_fsm_output: (),
            _marker_e: std::marker::PhantomData,
        };

        if use_for_leaf.get_value().unwrap_or(false) {
            for_leafs.push(leaf_closed_form_input.clone());
        }

        use crate::inputs::ClosedFormInputCompactForm;

        let leaf_closed_form_input_compact_form = ClosedFormInputCompactForm::from_full_form(
            cs,
            &leaf_closed_form_input,
            round_function,
        )?;
        use crate::glue::optimizable_queue::commit_encodable_item;
        let leaf_closed_form_input_committment =
            commit_encodable_item(cs, &leaf_closed_form_input_compact_form, round_function)?;

        // node case

        let input_for_node = NodeAggregationInputData {
            node_vk_committment: structured_input.observable_input.node_vk_committment,
            leaf_vk_committment: structured_input.observable_input.leaf_vk_committment,
            all_circuit_types_committment_for_leaf: structured_input
                .observable_input
                .all_circuit_types_committment_for_leaf,
            initial_log_queue_state: chunk_state.clone(),
        };

        let output_for_node_witness = if use_for_node.get_value().unwrap_or(false) {
            get_vec_witness_raw(
                &mut node_aggregation_results_witnesses,
                NodeAggregationOutputData::placeholder_witness(),
            )
        } else {
            Some(NodeAggregationOutputData::placeholder_witness())
        };

        let output_for_node =
            NodeAggregationOutputData::alloc_from_witness(cs, output_for_node_witness)?;

        let casted_aggregation_result_from_node = output_for_node.clone();
        let casted_aggregation_result_from_leaf = NodeAggregationOutputData {
            pair_with_x_x: output_for_leaf.pair_with_x_x,
            pair_with_x_y: output_for_leaf.pair_with_x_y,
            pair_with_generator_x: output_for_leaf.pair_with_generator_x,
            pair_with_generator_y: output_for_leaf.pair_with_generator_y,
        };

        let node_closed_form_input = NodeAggregationInputOutput {
            start_flag: Boolean::constant(true),
            completion_flag: Boolean::constant(true), // those do not matter
            observable_input: input_for_node,
            observable_output: output_for_node,
            hidden_fsm_input: (),
            hidden_fsm_output: (),
            _marker_e: std::marker::PhantomData,
        };

        if use_for_node.get_value().unwrap_or(false) {
            for_nodes.push(node_closed_form_input.clone());
        }

        let node_closed_form_input_compact_form = ClosedFormInputCompactForm::from_full_form(
            cs,
            &node_closed_form_input,
            round_function,
        )?;
        let node_closed_form_input_committment =
            commit_encodable_item(cs, &node_closed_form_input_compact_form, round_function)?;

        // select VK/padding/etc and push into vector

        // dbg!(&leaf_closed_form_input_committment.get_value());
        // dbg!(&node_closed_form_input_committment.get_value());

        let vk_to_use = Num::conditionally_select(
            cs,
            &use_for_node,
            &structured_input.observable_input.node_vk_committment,
            &structured_input.observable_input.leaf_vk_committment,
        )?;

        let vk_to_use = Num::conditionally_select(
            cs,
            &do_padding,
            &Num::Constant(padding_vk_committment),
            &vk_to_use,
        )?;

        // dbg!(&vk_to_use.get_value());

        let input_to_use = Num::conditionally_select(
            cs,
            &use_for_node,
            &node_closed_form_input_committment,
            &leaf_closed_form_input_committment,
        )?;

        let input_to_use = Num::conditionally_select(
            cs,
            &do_padding,
            &Num::Constant(padding_public_inputs[proof_idx]),
            &input_to_use,
        )?;

        // dbg!(&input_to_use.get_value());

        let mut casted_aggregation_result = NodeAggregationOutputData::conditionally_select(
            cs,
            &use_for_node,
            &casted_aggregation_result_from_node,
            &casted_aggregation_result_from_leaf,
        )?;

        let (
            padding_pair_with_gen_x,
            padding_pair_with_gen_y,
            padding_pair_with_x_x,
            padding_pair_with_x_y,
        ) = padding_aggregation_sets[proof_idx].clone();

        assert_eq!(
            casted_aggregation_result.pair_with_generator_x.len(),
            padding_pair_with_gen_x.len()
        );

        for (dst, src) in casted_aggregation_result
            .pair_with_generator_x
            .iter_mut()
            .chain(casted_aggregation_result.pair_with_generator_y.iter_mut())
            .chain(casted_aggregation_result.pair_with_x_x.iter_mut())
            .chain(casted_aggregation_result.pair_with_x_y.iter_mut())
            .zip(
                padding_pair_with_gen_x
                    .iter()
                    .chain(padding_pair_with_gen_y.iter())
                    .chain(padding_pair_with_x_x.iter())
                    .chain(padding_pair_with_x_y.iter()),
            )
        {
            *dst = Num::conditionally_select(cs, &do_padding, &Num::Constant(*src), &dst)?;
        }

        key_committments.push(vk_to_use);
        inputs.push(input_to_use);
        casted_aggregation_results.push(casted_aggregation_result);
    }

    recursion_requests_queue.enforce_to_be_empty(cs)?;

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
            padding_proofs[0].clone(),
            Some(casted_aggregation_results),
            round_function,
            vks_raw_elements_witness,
            padding_vk_encoding,
            g2_elements,
            num_proofs_to_aggregate,
        )?;

    let self_output = NodeAggregationOutputData {
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

    Ok((public_input, for_leafs, for_nodes, self_output))
}

use crate::glue::traits::*;
use crate::recursion::leaf_aggregation::LeafAggregationOutputData;
use crate::recursion::recursion_tree::AggregationParameters;
use crate::scheduler::RecursiveProofQueue;
use rescue_poseidon::CircuitGenericSponge;

pub fn aggregate_generic_inner<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    MG: MainGate<E>,
    T: TranscriptGadget<E>,
    P: HashParams<E, 2, 3>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const USE_MODIFIED_MAIN_GATE: bool,
>(
    cs: &mut CS,
    keys_committments: Vec<Num<E>>,
    inputs: Vec<Num<E>>,
    mut aggregation_proofs: Option<
        Vec<Proof<E, MainGateParametrizedCircuitWithNonlinearityAndLookups<E, MG>>>,
    >,
    aggregation_params: AggregationParameters<E, T, P, 2, 3>,
    rns_params: &'a RnsParameters<E, E::Fq>,
    padding_proof: Proof<E, MainGateParametrizedCircuitWithNonlinearityAndLookups<E, MG>>,
    aggregation_results: Option<Vec<NodeAggregationOutputData<E>>>,
    round_function: &R,
    mut vks_raw_elements_witness: Option<Vec<[E::Fr; VK_ENCODING_LENGTH]>>,
    padding_vk_encoding: [E::Fr; VK_ENCODING_LENGTH],
    g2_elements: Option<[E::G2Affine; 2]>,
    limit: usize,
) -> Result<[[[Num<E>; NUM_LIMBS]; 2]; 2], SynthesisError> {
    let geometry = if USE_MODIFIED_MAIN_GATE {
        GeometryHint::hint_for_reference_geometry_with_optimized_selectors()
    } else {
        GeometryHint::hint_for_reference_geometry()
    };
    // FS challenge for aggregation
    let mut fs_hasher = CircuitGenericSponge::new();

    let mut allocated_proofs = vec![];
    let mut allocated_vks = vec![];

    for idx in 0..limit {
        // we are ok to manipulate any witness values here, only the input matters
        // that later will be masked on queue emptiness

        let (proof, _) =
            get_vec_witness_raw_with_hint(&mut aggregation_proofs, padding_proof.clone());
        let rns_proof = ProofInRns {
            proof,
            rns_params: rns_params,
        };

        let proof_encoding: Vec<_> = rns_proof.encode()?.into_iter().map(|el| Some(el)).collect();
        let proof_encoding = allocate_vec_of_nums(cs, &proof_encoding)?;
        // absorb
        for n in proof_encoding.iter() {
            fs_hasher.absorb(cs, n.clone(), &aggregation_params.hash_params)?;
        }
        // and cast-allocate
        let proof =
            AllocatedProof::from_nums_and_geometry(cs, &proof_encoding, &geometry, rns_params)?;

        allocated_proofs.push(proof.clone());

        let vk_encoding = get_vec_witness_raw(&mut vks_raw_elements_witness, padding_vk_encoding);
        let vk_encoding = Num::alloc_multiple(cs, vk_encoding)?;
        use crate::glue::optimizable_queue::variable_length_hash;
        let leaf_hash = variable_length_hash(cs, &vk_encoding, round_function)?;
        leaf_hash.enforce_equal(cs, &keys_committments[idx])?;

        let vk = AllocatedVerificationKey::from_nums_and_geometry(
            cs,
            &vk_encoding,
            &geometry,
            rns_params,
        )?;
        allocated_vks.push(vk);
    }

    let mut num_aggregations_to_carry_on = 0;

    let mut aggregation_inputs = vec![];

    if let Some(previous_results) = aggregation_results {
        for agg_result in previous_results.into_iter() {
            for el in agg_result
                .pair_with_generator_x
                .iter()
                .chain(agg_result.pair_with_generator_y.iter())
                .chain(agg_result.pair_with_x_x.iter())
                .chain(agg_result.pair_with_x_y.iter())
            {
                fs_hasher.absorb(cs, el.clone(), &aggregation_params.hash_params)?;
            }

            let mut pair_with_gen_limbs = vec![];
            pair_with_gen_limbs.extend(agg_result.pair_with_generator_x);
            pair_with_gen_limbs.extend(agg_result.pair_with_generator_y);

            let mut pair_with_x_limbs = vec![];
            pair_with_x_limbs.extend(agg_result.pair_with_x_x);
            pair_with_x_limbs.extend(agg_result.pair_with_x_y);

            aggregation_inputs.push((pair_with_gen_limbs, pair_with_x_limbs));

            num_aggregations_to_carry_on += 1;
        }
    }

    let num_proofs_to_aggregate = limit;

    fs_hasher.pad_if_necessary();
    let multiopening_delinearization_challenge = fs_hasher
        .squeeze_num(cs, &aggregation_params.hash_params)?
        .expect("squeezed value");

    use crate::recursion::recursion_tree::final_aggregation_step;

    let result = aggregation_step::<_, _, MG, _, _, USE_MODIFIED_MAIN_GATE>(
        cs,
        num_proofs_to_aggregate,
        num_aggregations_to_carry_on,
        inputs,
        allocated_vks,
        allocated_proofs,
        aggregation_inputs,
        multiopening_delinearization_challenge,
        aggregation_params,
        rns_params,
        g2_elements,
    )?;

    Ok(result)
}

pub fn aggregation_step<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    MG: MainGate<E>,
    T: TranscriptGadget<E>,
    P: HashParams<E, 2, 3>,
    const USE_MODIFIED_MAIN_GATE: bool,
>(
    cs: &mut CS,
    num_proofs_to_aggregate: usize,
    num_aggregations_to_carry_on: usize,
    allocated_proofs_inputs: Vec<Num<E>>,
    allocated_vks: Vec<AllocatedVerificationKey<'a, E>>,
    allocated_proofs: Vec<AllocatedProof<'a, E>>,
    aggregation_allocated_inputs: Vec<(Vec<Num<E>>, Vec<Num<E>>)>,
    multiopening_delinearization_challenge: Num<E>,
    aggregation_params: AggregationParameters<E, T, P, 2, 3>,
    rns_params: &'a RnsParameters<E, E::Fq>,
    g2_elements: Option<[E::G2Affine; 2]>,
) -> Result<[[[Num<E>; NUM_LIMBS]; 2]; 2], SynthesisError> {
    let num_challenges = num_proofs_to_aggregate + num_aggregations_to_carry_on;

    // Ok, we are in a good state, so we can now recast encodings into the
    // affine points and perform an actual aggregation
    let mut aggregation_challenges = vec![];
    let mut current = multiopening_delinearization_challenge;
    aggregation_challenges.push(current);
    for _ in 1..num_challenges {
        current = current.mul(cs, &multiopening_delinearization_challenge)?;
        aggregation_challenges.push(current);
    }

    let (challenges_for_new_aggregation, challenges_for_already_aggregated) =
        aggregation_challenges.split_at(num_proofs_to_aggregate);

    // all proofs are valid in one way or another
    let validity_flags = vec![Boolean::constant(true); num_proofs_to_aggregate];

    let aggregation_state = perform_aggregation::<_, _, T, USE_MODIFIED_MAIN_GATE>(
        cs,
        &validity_flags,
        &allocated_proofs_inputs,
        &allocated_vks,
        &allocated_proofs,
        &challenges_for_new_aggregation,
        &rns_params,
        aggregation_params.base_placeholder_point,
        &aggregation_params.transcript_params,
    )?;

    let AggregationState::<E> {
        mut pair_with_generator,
        mut pair_with_x,
        scalar_to_mul_with_generator,
    } = aggregation_state;

    use crate::recursion::zeroable_point::PointAffine;

    let generator = PointAffine::constant(E::G1Affine::one(), rns_params);
    let scalar = scalar_to_mul_with_generator;

    let pair = (scalar, generator);
    pair.accumulate_into(cs, &mut pair_with_generator)?;

    // mix in aggregation results from previous levels

    let mut allocated_pair_with_gen_previous_results = vec![];
    let mut allocated_pair_with_x_previous_results = vec![];

    for (pair_with_generator_limbs, pair_with_x_limbs) in aggregation_allocated_inputs.into_iter() {
        let pair_with_gen_point: PointAffine<E, E::G1Affine> =
            PointAffine::allocate_from_in_field_binary_limbs(
                cs,
                &pair_with_generator_limbs,
                &rns_params,
            )?;

        let pair_with_x_point: PointAffine<E, E::G1Affine> =
            PointAffine::allocate_from_in_field_binary_limbs(cs, &pair_with_x_limbs, &rns_params)?;

        allocated_pair_with_gen_previous_results.push(pair_with_gen_point);
        allocated_pair_with_x_previous_results.push(pair_with_x_point);
    }

    assert_eq!(
        allocated_pair_with_gen_previous_results.len(),
        challenges_for_already_aggregated.len()
    );

    for ((previous_for_pair_with_gen, previous_for_pair_with_x), challenge) in
        allocated_pair_with_gen_previous_results
            .into_iter()
            .zip(allocated_pair_with_x_previous_results.into_iter())
            .zip(challenges_for_already_aggregated.iter())
    {
        let pair = (*challenge, previous_for_pair_with_gen);
        pair.accumulate_into(cs, &mut pair_with_generator)?;

        let pair = (*challenge, previous_for_pair_with_x);
        pair.accumulate_into(cs, &mut pair_with_x)?;
    }

    let final_pair_with_generator = pair_with_generator.finalize_completely(cs)?;
    let final_pair_with_x = pair_with_x.finalize_completely(cs)?;

    match (
        final_pair_with_generator.get_value(),
        final_pair_with_x.get_value(),
        g2_elements,
    ) {
        (Some(pair_with_generator), Some(pair_with_x), Some(g2_elements)) => {
            let valid = E::final_exponentiation(&E::miller_loop(&[
                (&pair_with_generator.prepare(), &g2_elements[0].prepare()),
                (&pair_with_x.prepare(), &g2_elements[1].prepare()),
            ]))
            .ok_or(SynthesisError::Unsatisfiable)?
                == E::Fqk::one();
            assert!(valid);
        }
        _ => {}
    }

    let pair_with_gen_encoding = encode_affine_point(cs, final_pair_with_generator)?;
    let pair_with_x_encoding = encode_affine_point(cs, final_pair_with_x)?;

    use std::convert::TryInto;

    let (pair_with_generator_x, pair_with_generator_y) = pair_with_gen_encoding.split_at(NUM_LIMBS);
    let pair_with_generator_x: [Num<E>; NUM_LIMBS] =
        pair_with_generator_x.try_into().expect("length must match");
    let pair_with_generator_y: [Num<E>; NUM_LIMBS] =
        pair_with_generator_y.try_into().expect("length must match");

    let (pair_with_x_x, pair_with_x_y) = pair_with_x_encoding.split_at(NUM_LIMBS);
    let pair_with_x_x: [Num<E>; NUM_LIMBS] = pair_with_x_x.try_into().expect("length must match");
    let pair_with_x_y: [Num<E>; NUM_LIMBS] = pair_with_x_y.try_into().expect("length must match");

    Ok([
        [pair_with_generator_x, pair_with_generator_y],
        [pair_with_x_x, pair_with_x_y],
    ])
}
