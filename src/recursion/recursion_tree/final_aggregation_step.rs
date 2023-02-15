use super::*;

pub fn final_aggregation_step<
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
    aggregation_validity_flags: Vec<Boolean>,
    multiopening_delinearization_challenge: Num<E>,
    aggregation_params: AggregationParameters<E, T, P, 2, 3>,
    rns_params: &'a RnsParameters<E, E::Fq>,
    g2_elements: Option<[E::G2Affine; 2]>,
    reporting_function: Option<Box<dyn FnOnce(E::G1Affine, E::G1Affine, bool) -> ()>>,
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

    let generator = PointAffine::constant(E::G1Affine::one(), rns_params);
    let scalar = scalar_to_mul_with_generator;

    let pair = (scalar, generator);
    pair.accumulate_into(cs, &mut pair_with_generator)?;

    // mix in aggregation results from previous levels

    let mut allocated_pair_with_gen_previous_results = vec![];
    let mut allocated_pair_with_x_previous_results = vec![];

    for ((pair_with_generator_limbs, pair_with_x_limbs), execute) in aggregation_allocated_inputs
        .into_iter()
        .zip(aggregation_validity_flags.into_iter())
    {
        let pair_with_gen_point: PointAffine<E, E::G1Affine> =
            PointAffine::allocate_from_in_field_binary_limbs(
                cs,
                &pair_with_generator_limbs,
                &rns_params,
            )?;

        let pair_with_x_point: PointAffine<E, E::G1Affine> =
            PointAffine::allocate_from_in_field_binary_limbs(cs, &pair_with_x_limbs, &rns_params)?;

        // mask
        let pair_with_gen_point = mask_point(cs, &execute, pair_with_gen_point)?;
        let pair_with_x_point = mask_point(cs, &execute, pair_with_x_point)?;

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

            if let Some(func) = reporting_function {
                func(pair_with_generator, pair_with_x, valid);
            }
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
