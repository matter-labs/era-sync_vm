use crate::bellman::SynthesisError;
use crate::data_structures::markers::*;
use crate::derivative::*;
use crate::ff::*;
use crate::pairing::{CurveAffine, CurveProjective, Engine};
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::bigint::field::*;
use franklin_crypto::plonk::circuit::bigint::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::curve::endomorphism::*;
use franklin_crypto::plonk::circuit::curve::sw_affine::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::plonk::circuit::Assignment;

use crate::circuit_structures::byte::*;
use crate::circuit_structures::traits::*;
use crate::circuit_structures::utils::*;
use crate::project;
use crate::traits::*;
use franklin_crypto::plonk::circuit::simple_term::*;
use franklin_crypto::rescue::RescueHashParams;

pub mod accumulator;
pub mod aggregation;
pub mod kate;
pub mod partial_accumulator;
pub mod recursion_tree;
pub mod transcript;
pub mod utils;
pub mod zeroable_point;

use crate::utils::{bn254_rescue_params, AWIDTH_VALUE, SWIDTH_VALUE};
use rescue_poseidon::{CustomGate, HashParams, RescueParams};
pub mod leaf_aggregation;
pub mod node_aggregation;

use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::proof::Proof;
use crate::bellman::plonk::better_better_cs::setup::VerificationKey;

use self::aggregation::*;
use self::partial_accumulator::*;
use self::transcript::*;

pub(crate) fn perform_aggregation<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    T: TranscriptGadget<E>,
    const USE_MODIFIED_MAIN_GATE: bool,
>(
    cs: &mut CS,
    validity_flags: &[Boolean],
    inputs: &[Num<E>],
    vks: &[AllocatedVerificationKey<'a, E>],
    proofs: &[AllocatedProof<'a, E>],
    fs_challenges: &[Num<E>],
    rns_params: &'a RnsParameters<E, E::Fq>,
    base_placeholder_point: E::G1Affine,
    transcript_params: &'a T::Params,
) -> Result<AggregationState<'a, E>, SynthesisError> {
    assert_eq!(validity_flags.len(), inputs.len());
    assert_eq!(validity_flags.len(), vks.len());
    assert_eq!(validity_flags.len(), proofs.len());
    assert_eq!(validity_flags.len(), fs_challenges.len());

    let factor = E::Fr::multiplicative_generator();

    let pair_with_gen_accumulator = PartialHomomorphicAccumulator::init(
        cs,
        base_placeholder_point,
        factor,
        rns_params,
        Num::Constant(E::Fr::zero()),
    )?;

    let pair_with_x_accumulator = PartialHomomorphicAccumulator::init(
        cs,
        base_placeholder_point,
        factor,
        rns_params,
        Num::Constant(E::Fr::zero()),
    )?;

    let mut aggregation_state = AggregationState::<E> {
        pair_with_generator: pair_with_gen_accumulator,
        pair_with_x: pair_with_x_accumulator,
        scalar_to_mul_with_generator: Num::Constant(E::Fr::zero()),
    };

    for (_idx, ((((valid, input), vk), proof), challenge)) in validity_flags
        .iter()
        .zip(inputs.iter())
        .zip(vks.iter())
        .zip(proofs.iter())
        .zip(fs_challenges.iter())
        .enumerate()
    {
        let execute = valid;
        let proof_input_is_valid = Num::equals(cs, &input, &proof.inputs[0])?;
        can_not_be_false_if_flagged(cs, &proof_input_is_valid, &execute)?;

        // So we know that input is what we expect and can just run the proof

        let (is_valid_proof, add_to_generator) =
            aggregate_single_allocated_for_reference_geometry::<_, T, _, USE_MODIFIED_MAIN_GATE>(
                cs,
                &proof,
                &transcript_params,
                &mut aggregation_state.pair_with_generator,
                &mut aggregation_state.pair_with_x,
                &vk,
                &challenge,
            )?;

        can_not_be_false_if_flagged(cs, &is_valid_proof, &execute)?;

        aggregation_state.scalar_to_mul_with_generator = aggregation_state
            .scalar_to_mul_with_generator
            .add(cs, &add_to_generator)?;
    }

    Ok(aggregation_state)
}

use self::utils::*;

pub const RANGE_CHECK_TABLE_BIT_WIDTH: usize = 16;
// pub const RANGE_CHECK_TABLE_BIT_WIDTH: usize = 17;
pub const DEFAULT_RANGE_CONSTRAINT_INFO: RangeConstraintInfo = RangeConstraintInfo {
    minimal_multiple: RANGE_CHECK_TABLE_BIT_WIDTH,
    optimal_multiple: RANGE_CHECK_TABLE_BIT_WIDTH,
    multiples_per_gate: 1,
    linear_terms_used: 3,
    strategy: RangeConstraintStrategy::SingleTableInvocation,
};

use crate::pairing::bn256::{Bn256, Fq};

pub fn get_prefered_rns_params() -> RnsParameters<Bn256, Fq> {
    let rns_params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
        80,
        100,
        4,
        DEFAULT_RANGE_CONSTRAINT_INFO,
        true,
    );

    rns_params
}

// pub fn get_prefered_rns_params() -> RnsParameters::<Bn256, Fq> {
//     let rns_params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
//         68,
//         110,
//         4,
//         DEFAULT_RANGE_CONSTRAINT_INFO,
//         true
//     );

//     rns_params
// }

pub fn get_prefered_hash_params() -> RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE> {
    bn254_rescue_params()

    // let mut params = RescueParams::default();

    // params.use_custom_gate(CustomGate::QuinticWidth4);

    // params
}

pub fn get_prefered_committer(
) -> GenericHasher<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>
{
    GenericHasher::new_from_params(&get_prefered_hash_params())
}

pub fn get_base_placeholder_point_for_accumulators() -> <Bn256 as Engine>::G1Affine {
    let point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<
        <Bn256 as Engine>::G1Affine,
    >(b"G1Acc", 1)[0];

    point
}

pub trait Accumulator<E: Engine> {
    type NonTrivialElement: Clone + std::fmt::Debug;
    type TrivialElement: Clone + std::fmt::Debug;
    type Result: Clone + std::fmt::Debug;
    fn get_placeholders(&mut self) -> (Self::TrivialElement, Self::NonTrivialElement);
    fn add_non_trivial<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        element: Self::NonTrivialElement,
    ) -> Result<(), SynthesisError>;
    fn add_trivial<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        element: Self::TrivialElement,
    ) -> Result<(), SynthesisError>;
    fn finalize<CS: ConstraintSystem<E>>(self, cs: &mut CS)
        -> Result<Self::Result, SynthesisError>;
}

pub trait Accumulable<E: Engine, A: Accumulator<E>> {
    fn accumulate_into<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        accumulator: &mut A,
    ) -> Result<(), SynthesisError>;
}

pub type RescueTranscriptForRecursion<'a> = GenericTranscriptForRNSInFieldOnly<
    'a,
    crate::pairing::bn256::Bn256,
    RescueParams<crate::pairing::bn256::Bn256, 2, 3>,
    2,
    3,
>;
