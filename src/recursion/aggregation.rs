use super::accumulator::*;
use super::kate::*;
use super::node_aggregation::ZkSyncParametricCircuit;
use super::partial_accumulator::*;
use super::transcript::*;
use super::zeroable_point::*;
use super::*;

use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::proof::Proof;
use crate::bellman::plonk::better_better_cs::setup::VerificationKey;

use franklin_crypto::plonk::circuit::custom_rescue_gate::Rescue5CustomGate;
use franklin_crypto::plonk::circuit::verifier_circuit::helper_functions::*;

use super::utils::*;
use crate::circuit_structures::traits::*;
use crate::traits::*;

use crate::derivative::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct CircuitWithNonlinearityAndLookups;

impl<E: Engine> Circuit<E> for CircuitWithNonlinearityAndLookups {
    type MainGate = Width4MainGateWithDNext;
    // type MainGate = SelectorOptimizedWidth4MainGateWithDNext;

    fn synthesize<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<(), SynthesisError> {
        unimplemented!("This is a marker circuit and must not be used for synthesis");
    }
    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(vec![
            Self::MainGate::default().into_internal(),
            Rescue5CustomGate::default().into_internal(),
        ])
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, Default(bound = ""))]
pub struct MainGateParametrizedCircuitWithNonlinearityAndLookups<
    E: Engine,
    MG: MainGate<E> = Width4MainGateWithDNext,
> {
    pub _marker_e: std::marker::PhantomData<E>,
    pub _marker_mg: std::marker::PhantomData<MG>,
}

impl<E: Engine, MG: MainGate<E>> Circuit<E>
    for MainGateParametrizedCircuitWithNonlinearityAndLookups<E, MG>
{
    type MainGate = MG;

    fn synthesize<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<(), SynthesisError> {
        unimplemented!("This is a marker circuit and must not be used for synthesis");
    }
    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(vec![
            Self::MainGate::default().into_internal(),
            Rescue5CustomGate::default().into_internal(),
        ])
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GeometryHint {
    pub num_state_polys: usize,
    pub num_inputs: usize,
    pub total_num_gate_setup_polys: usize,
    pub total_num_gate_selectors: usize,
    pub state_polys_opening_locations_at_dilations: Vec<(usize, usize)>,
    pub gate_setup_openings_at_z_locations: Vec<(usize, usize)>,
    pub gate_selectors_openings_at_z_locations: Vec<usize>,
}

impl GeometryHint {
    pub fn hint_for_reference_geometry() -> Self {
        Self {
            num_state_polys: 4,
            num_inputs: 1,
            total_num_gate_setup_polys: 7, // only main gate 4 + 1 + 1 + 1
            total_num_gate_selectors: 2,   // main and non-linearity
            // oped D(z*omega)
            state_polys_opening_locations_at_dilations: vec![(3, 1)],
            // there are no setup polynomials being opened anywhere
            gate_setup_openings_at_z_locations: vec![],
            // only selector at of main gate is opened at z
            gate_selectors_openings_at_z_locations: vec![0],
        }
    }

    pub fn hint_for_reference_geometry_with_optimized_selectors() -> Self {
        Self {
            num_state_polys: 4,
            num_inputs: 1,
            total_num_gate_setup_polys: 8, // only main gate 4 + 1 + 1 + 1 + 1
            total_num_gate_selectors: 2,   // main and non-linearity
            // oped D(z*omega)
            state_polys_opening_locations_at_dilations: vec![(3, 1)],
            // there are no setup polynomials being opened anywhere
            gate_setup_openings_at_z_locations: vec![],
            // only selector at of main gate is opened at z
            gate_selectors_openings_at_z_locations: vec![0],
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct AllocatedVerificationKey<'a, E: Engine> {
    pub num_inputs: usize,
    pub n_next_power_of_two: Num<E>,
    pub omega: Num<E>,

    pub gate_setup_commitments: Vec<PointAffine<'a, E, E::G1Affine>>,
    pub gate_selectors_commitments: Vec<PointAffine<'a, E, E::G1Affine>>,
    pub permutation_commitments: Vec<PointAffine<'a, E, E::G1Affine>>,

    pub lookup_selector_commitment: PointAffine<'a, E, E::G1Affine>,
    pub lookup_tables_commitments: Vec<PointAffine<'a, E, E::G1Affine>>,
    pub lookup_table_type_commitment: PointAffine<'a, E, E::G1Affine>,

    pub non_residues: Vec<Num<E>>,
}

#[derive(Clone)]
pub struct VkInRns<'a, E: Engine> {
    pub vk: Option<VerificationKey<E, ZkSyncParametricCircuit<E>>>,

    //#[derivative(Debug="ignore")]
    pub rns_params: &'a RnsParameters<E, E::Fq>,
}

impl<'a, E: Engine> ArithmeticEncodable<E> for VkInRns<'a, E> {
    fn encoding_length_is_constant() -> bool {
        false
    }
    fn encoding_length() -> usize {
        unreachable!("this structure has non-constant length, use `encoding_length_for_instance`");
    }
    fn encoding_length_for_instance(&self) -> usize {
        let num_limbs_per_point = self.rns_params.num_limbs_for_in_field_representation * 2;

        // let num_points = 7 + 2 + 4 + 1 + 4 + 1; // 19
        let num_points = 8 + 2 + 4 + 1 + 4 + 1; // 19
        let num_scalars = 1 + 1 + 3;

        let total = num_limbs_per_point * num_points + num_scalars;

        assert_eq!(
            total,
            crate::recursion::node_aggregation::VK_ENCODING_LENGTH
        );

        total
    }

    #[track_caller]
    fn encode(&self) -> Result<Vec<E::Fr>, SynthesisError> {
        let vk = self
            .vk
            .as_ref()
            .expect("must have a verification key witness")
            .clone();

        let mut encoding = vec![];

        assert_eq!(vk.num_inputs, 1);

        let n_next_power_of_two = E::Fr::from_str(&vk.n.next_power_of_two().to_string()).unwrap();
        encoding.push(n_next_power_of_two);

        let domain =
            crate::bellman::plonk::domains::Domain::new_for_size(vk.n.next_power_of_two() as u64)?;
        encoding.push(domain.generator);

        write_g1_points_vec(&vk.gate_setup_commitments, &mut encoding, &self.rns_params);
        write_g1_points_vec(
            &vk.gate_selectors_commitments,
            &mut encoding,
            &self.rns_params,
        );
        write_g1_points_vec(&vk.permutation_commitments, &mut encoding, &self.rns_params);

        write_g1_point(
            vk.lookup_selector_commitment
                .expect("must exist in reference geometry"),
            &mut encoding,
            &self.rns_params,
        );
        write_g1_points_vec(
            &vk.lookup_tables_commitments,
            &mut encoding,
            &self.rns_params,
        );
        write_g1_point(
            vk.lookup_table_type_commitment
                .expect("must exist in reference geometry"),
            &mut encoding,
            &self.rns_params,
        );

        encoding.extend_from_slice(&vk.non_residues);

        assert_eq!(encoding.len(), self.encoding_length_for_instance());

        Ok(encoding)
    }
}

impl<'a, E: Engine> ArithmeticCommitable<E> for VkInRns<'a, E> {}

impl<'a, E: Engine> AllocatedVerificationKey<'a, E> {
    pub fn from_witness_and_geometry<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: &[Option<E::Fr>],
        geometry: &GeometryHint,
        rns_params: &'a RnsParameters<E, E::Fq>,
    ) -> Result<Self, SynthesisError> {
        let as_nums = allocate_vec_of_nums(cs, witness)?;

        Self::from_nums_and_geometry(cs, &as_nums, geometry, rns_params)
    }

    pub fn from_nums_and_geometry<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: &[Num<E>],
        geometry: &GeometryHint,
        rns_params: &'a RnsParameters<E, E::Fq>,
    ) -> Result<Self, SynthesisError> {
        let element_per_point = rns_params.num_limbs_for_in_field_representation * 2;

        let mut s = witness;

        let n_next_power_of_two = take(&mut s, 1)[0];
        let omega = take(&mut s, 1)[0];
        let gate_setup_commitments = allocate_vec_of_g1s(
            cs,
            take(
                &mut s,
                element_per_point * geometry.total_num_gate_setup_polys,
            ),
            rns_params,
        )?;
        let gate_selectors_commitments = allocate_vec_of_g1s(
            cs,
            take(
                &mut s,
                element_per_point * geometry.total_num_gate_selectors,
            ),
            rns_params,
        )?;
        let permutation_commitments = allocate_vec_of_g1s(
            cs,
            take(&mut s, element_per_point * geometry.num_state_polys),
            rns_params,
        )?;
        let lookup_selector_commitment =
            allocate_g1_from_witness(cs, take(&mut s, element_per_point), rns_params)?;
        let lookup_tables_commitments =
            allocate_vec_of_g1s(cs, take(&mut s, element_per_point * 4), rns_params)?;
        let lookup_table_type_commitment =
            allocate_g1_from_witness(cs, take(&mut s, element_per_point), rns_params)?;
        let non_residues = take(&mut s, geometry.num_state_polys - 1).to_vec();

        assert_eq!(s.len(), 0);

        let new = Self {
            num_inputs: 1,
            n_next_power_of_two,
            omega,
            gate_setup_commitments,
            gate_selectors_commitments,
            permutation_commitments,
            lookup_selector_commitment,
            lookup_tables_commitments,
            lookup_table_type_commitment,
            non_residues,
        };

        Ok(new)
    }
}

#[derive(Clone)]
pub struct ProofInRns<'a, E: Engine, C: Clone + Circuit<E> = CircuitWithNonlinearityAndLookups> {
    pub proof: Option<Proof<E, C>>,

    //#[derivative(Debug="ignore")]
    pub rns_params: &'a RnsParameters<E, E::Fq>,
}

impl<'a, E: Engine, C: Clone + Send + Sync + Circuit<E>> ArithmeticEncodable<E>
    for ProofInRns<'a, E, C>
{
    fn encoding_length_is_constant() -> bool {
        false
    }
    fn encoding_length() -> usize {
        unreachable!("this structure has non-constant length, use `encoding_length_for_instance`");
    }
    fn encoding_length_for_instance(&self) -> usize {
        let num_limbs_per_point = self.rns_params.num_limbs_for_in_field_representation * 2;

        let num_points = 4 + 1 + 1 + 1 + 4 + 2; // 13
        let num_scalars = 1 + 4 + 1 + 1 + 3 + 1 + 6 + 2;

        num_limbs_per_point * num_points + num_scalars
    }

    #[track_caller]
    fn encode(&self) -> Result<Vec<E::Fr>, SynthesisError> {
        let proof = self
            .proof
            .as_ref()
            .expect("must have a proof witness")
            .clone();

        let mut encoding = vec![];

        assert_eq!(proof.inputs.len(), 1);
        encoding.push(proof.inputs[0]);

        assert_eq!(proof.state_polys_commitments.len(), 4);
        write_g1_points_vec(
            &proof.state_polys_commitments,
            &mut encoding,
            &self.rns_params,
        );

        write_g1_point(
            proof.copy_permutation_grand_product_commitment,
            &mut encoding,
            &self.rns_params,
        );

        write_g1_point(
            proof
                .lookup_s_poly_commitment
                .expect("must exist in reference geometry"),
            &mut encoding,
            &self.rns_params,
        );
        write_g1_point(
            proof
                .lookup_grand_product_commitment
                .expect("must exist in reference geometry"),
            &mut encoding,
            &self.rns_params,
        );

        assert_eq!(proof.quotient_poly_parts_commitments.len(), 4);
        write_g1_points_vec(
            &proof.quotient_poly_parts_commitments,
            &mut encoding,
            &self.rns_params,
        );

        assert_eq!(proof.state_polys_openings_at_z.len(), 4);
        encoding.extend_from_slice(&proof.state_polys_openings_at_z);

        assert_eq!(proof.state_polys_openings_at_dilations.len(), 1);
        encoding.extend(
            proof
                .state_polys_openings_at_dilations
                .iter()
                .cloned()
                .map(|el| el.2),
        );

        assert_eq!(proof.gate_setup_openings_at_z.len(), 0);
        encoding.extend(
            proof
                .gate_setup_openings_at_z
                .iter()
                .cloned()
                .map(|el| el.2),
        );

        assert_eq!(proof.gate_selectors_openings_at_z.len(), 1);
        encoding.extend(
            proof
                .gate_selectors_openings_at_z
                .iter()
                .cloned()
                .map(|el| el.1),
        );

        assert_eq!(proof.copy_permutation_polys_openings_at_z.len(), 3);
        encoding.extend_from_slice(&proof.copy_permutation_polys_openings_at_z);

        encoding.push(proof.copy_permutation_grand_product_opening_at_z_omega);

        encoding.push(
            proof
                .lookup_s_poly_opening_at_z_omega
                .expect("must exist in reference geometry"),
        );
        encoding.push(
            proof
                .lookup_grand_product_opening_at_z_omega
                .expect("must exist in reference geometry"),
        );
        encoding.push(
            proof
                .lookup_t_poly_opening_at_z
                .expect("must exist in reference geometry"),
        );
        encoding.push(
            proof
                .lookup_t_poly_opening_at_z_omega
                .expect("must exist in reference geometry"),
        );
        encoding.push(
            proof
                .lookup_selector_poly_opening_at_z
                .expect("must exist in reference geometry"),
        );
        encoding.push(
            proof
                .lookup_table_type_poly_opening_at_z
                .expect("must exist in reference geometry"),
        );

        encoding.push(proof.quotient_poly_opening_at_z);
        encoding.push(proof.linearization_poly_opening_at_z);

        write_g1_point(proof.opening_proof_at_z, &mut encoding, &self.rns_params);
        write_g1_point(
            proof.opening_proof_at_z_omega,
            &mut encoding,
            &self.rns_params,
        );

        assert_eq!(encoding.len(), self.encoding_length_for_instance());

        Ok(encoding)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct AllocatedProof<'a, E: Engine> {
    pub inputs: Vec<Num<E>>,
    pub state_polys_commitments: Vec<PointAffine<'a, E, E::G1Affine>>,
    pub copy_permutation_grand_product_commitment: PointAffine<'a, E, E::G1Affine>,

    pub lookup_s_poly_commitment: PointAffine<'a, E, E::G1Affine>,
    pub lookup_grand_product_commitment: PointAffine<'a, E, E::G1Affine>,

    pub quotient_poly_parts_commitments: Vec<PointAffine<'a, E, E::G1Affine>>,

    pub state_polys_openings_at_z: Vec<Num<E>>,

    pub state_polys_openings_at_dilations: Vec<Num<E>>,

    pub gate_setup_openings_at_z: Vec<Num<E>>,
    pub gate_selectors_openings_at_z: Vec<Num<E>>,

    pub copy_permutation_polys_openings_at_z: Vec<Num<E>>,
    pub copy_permutation_grand_product_opening_at_z_omega: Num<E>,

    pub lookup_s_poly_opening_at_z_omega: Num<E>,
    pub lookup_grand_product_opening_at_z_omega: Num<E>,

    pub lookup_t_poly_opening_at_z: Num<E>,
    pub lookup_t_poly_opening_at_z_omega: Num<E>,

    pub lookup_selector_poly_opening_at_z: Num<E>,
    pub lookup_table_type_poly_opening_at_z: Num<E>,

    pub quotient_poly_opening_at_z: Num<E>,

    pub linearization_poly_opening_at_z: Num<E>,

    pub opening_proof_at_z: PointAffine<'a, E, E::G1Affine>,
    pub opening_proof_at_z_omega: PointAffine<'a, E, E::G1Affine>,
}

impl<'a, E: Engine> AllocatedProof<'a, E> {
    pub fn from_witness_and_geometry<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: &[Option<E::Fr>],
        geometry: &GeometryHint,
        rns_params: &'a RnsParameters<E, E::Fq>,
    ) -> Result<Self, SynthesisError> {
        let as_nums = allocate_vec_of_nums(cs, witness)?;

        Self::from_nums_and_geometry(cs, &as_nums, geometry, rns_params)
    }

    pub fn from_nums_and_geometry<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: &[Num<E>],
        geometry: &GeometryHint,
        rns_params: &'a RnsParameters<E, E::Fq>,
    ) -> Result<Self, SynthesisError> {
        let mut s = witness;
        let inputs = take(&mut s, geometry.num_inputs).to_vec();
        assert_eq!(inputs.len(), 1);

        let element_per_point = rns_params.num_limbs_for_in_field_representation * 2;
        let state_polys_commitments = allocate_vec_of_g1s(
            cs,
            take(&mut s, element_per_point * geometry.num_state_polys),
            rns_params,
        )?;

        let copy_permutation_grand_product_commitment =
            allocate_g1_from_witness(cs, take(&mut s, element_per_point), rns_params)?;

        let lookup_s_poly_commitment =
            allocate_g1_from_witness(cs, take(&mut s, element_per_point), rns_params)?;
        let lookup_grand_product_commitment =
            allocate_g1_from_witness(cs, take(&mut s, element_per_point), rns_params)?;

        let quotient_poly_parts_commitments =
            allocate_vec_of_g1s(cs, take(&mut s, element_per_point * 4), rns_params)?;

        let state_polys_openings_at_z = take(&mut s, geometry.num_state_polys).to_vec();

        let state_polys_openings_at_dilations = take(
            &mut s,
            geometry.state_polys_opening_locations_at_dilations.len(),
        )
        .to_vec();

        let gate_setup_openings_at_z =
            take(&mut s, geometry.gate_setup_openings_at_z_locations.len()).to_vec();
        let gate_selectors_openings_at_z = take(
            &mut s,
            geometry.gate_selectors_openings_at_z_locations.len(),
        )
        .to_vec();

        let copy_permutation_polys_openings_at_z =
            take(&mut s, geometry.num_state_polys - 1).to_vec();
        let copy_permutation_grand_product_opening_at_z_omega = take(&mut s, 1)[0];

        let lookup_s_poly_opening_at_z_omega = take(&mut s, 1)[0];
        let lookup_grand_product_opening_at_z_omega = take(&mut s, 1)[0];
        let lookup_t_poly_opening_at_z = take(&mut s, 1)[0];
        let lookup_t_poly_opening_at_z_omega = take(&mut s, 1)[0];
        let lookup_selector_poly_opening_at_z = take(&mut s, 1)[0];
        let lookup_table_type_poly_opening_at_z = take(&mut s, 1)[0];

        let quotient_poly_opening_at_z = take(&mut s, 1)[0];
        let linearization_poly_opening_at_z = take(&mut s, 1)[0];

        let opening_proof_at_z =
            allocate_g1_from_witness(cs, take(&mut s, element_per_point), rns_params)?;
        let opening_proof_at_z_omega =
            allocate_g1_from_witness(cs, take(&mut s, element_per_point), rns_params)?;

        assert!(s.is_empty());

        let new = Self {
            inputs,
            state_polys_commitments,
            copy_permutation_grand_product_commitment,
            lookup_s_poly_commitment,
            lookup_grand_product_commitment,
            quotient_poly_parts_commitments,
            state_polys_openings_at_z,
            state_polys_openings_at_dilations,
            gate_setup_openings_at_z,
            gate_selectors_openings_at_z,
            copy_permutation_polys_openings_at_z,
            copy_permutation_grand_product_opening_at_z_omega,
            lookup_s_poly_opening_at_z_omega,
            lookup_grand_product_opening_at_z_omega,
            lookup_t_poly_opening_at_z,
            lookup_t_poly_opening_at_z_omega,
            lookup_selector_poly_opening_at_z,
            lookup_table_type_poly_opening_at_z,
            quotient_poly_opening_at_z,
            linearization_poly_opening_at_z,
            opening_proof_at_z,
            opening_proof_at_z_omega,
        };

        Ok(new)
    }
}

pub(crate) struct AggregationState<'a, E: Engine> {
    pub(crate) pair_with_generator: PartialHomomorphicAccumulator<'a, E>,
    pub(crate) pair_with_x: PartialHomomorphicAccumulator<'a, E>,
    pub(crate) scalar_to_mul_with_generator: Num<E>,
}

pub fn aggregate_single_for_reference_geometry<
    'a,
    E: Engine,
    T: TranscriptGadget<E>,
    CS: ConstraintSystem<E>,
    const USE_MODIFIED_MAIN_GATE: bool,
>(
    cs: &mut CS,
    proof_witness: ProofInRns<'a, E>,
    transcript_params: &'a T::Params,
    partial_accumulator_pair_with_generator: &mut PartialHomomorphicAccumulator<'a, E>,
    partial_accumulator_pair_with_x: &mut PartialHomomorphicAccumulator<'a, E>,
    vk: &AllocatedVerificationKey<'a, E>,
    multiopening_delinearization_challenge: &Num<E>,
    rns_params: &'a RnsParameters<E, E::Fq>,
) -> Result<(Boolean, Num<E>), SynthesisError> {
    let geometry = if USE_MODIFIED_MAIN_GATE {
        GeometryHint::hint_for_reference_geometry_with_optimized_selectors()
    } else {
        GeometryHint::hint_for_reference_geometry()
    };

    let proof_data = if proof_witness.proof.is_some() {
        let witness_values: Vec<Option<E::Fr>> = proof_witness
            .encode()?
            .into_iter()
            .map(|el| Some(el))
            .collect();

        witness_values
    } else {
        vec![None; proof_witness.encoding_length_for_instance()]
    };

    let proof =
        AllocatedProof::from_witness_and_geometry(cs, &proof_data[..], &geometry, rns_params)?;

    let res = aggregate_single_allocated_for_reference_geometry::<E, T, CS, USE_MODIFIED_MAIN_GATE>(
        cs,
        &proof,
        transcript_params,
        partial_accumulator_pair_with_generator,
        partial_accumulator_pair_with_x,
        vk,
        multiopening_delinearization_challenge,
    )?;

    Ok(res)
}

#[track_caller]
pub fn aggregate_single_allocated_for_reference_geometry<
    'a,
    E: Engine,
    T: TranscriptGadget<E>,
    CS: ConstraintSystem<E>,
    const USE_MODIFIED_MAIN_GATE: bool,
>(
    cs: &mut CS,
    proof: &AllocatedProof<'a, E>,
    transcript_params: &'a T::Params,
    partial_accumulator_pair_with_generator: &mut PartialHomomorphicAccumulator<'a, E>,
    partial_accumulator_pair_with_x: &mut PartialHomomorphicAccumulator<'a, E>,
    vk: &AllocatedVerificationKey<'a, E>,
    multiopening_delinearization_challenge: &Num<E>,
) -> Result<(Boolean, Num<E>), SynthesisError> {
    let geometry = if USE_MODIFIED_MAIN_GATE {
        GeometryHint::hint_for_reference_geometry_with_optimized_selectors()
    } else {
        GeometryHint::hint_for_reference_geometry()
    };

    let mut transcript = T::new(transcript_params);

    for inp in proof.inputs.iter() {
        transcript.commit_scalar(cs, inp.clone())?;
    }

    assert_eq!(
        proof.state_polys_commitments.len(),
        geometry.num_state_polys
    );

    for p in proof.state_polys_commitments.iter() {
        transcript.commit_point(cs, p)?;
    }

    let eta = transcript.get_challenge(cs)?;

    transcript.commit_point(cs, &proof.lookup_s_poly_commitment)?;

    let beta_for_copy_permutation = transcript.get_challenge(cs)?;
    let gamma_for_copy_permutation = transcript.get_challenge(cs)?;

    transcript.commit_point(cs, &proof.copy_permutation_grand_product_commitment)?;

    let beta_for_lookup = transcript.get_challenge(cs)?;
    let gamma_for_lookup = transcript.get_challenge(cs)?;

    transcript.commit_point(cs, &proof.lookup_grand_product_commitment)?;

    let alpha = transcript.get_challenge(cs)?;

    let total_powers_of_alpha_for_gates = 1 + 3;

    let mut powers_of_alpha_for_gates = vec![];

    let mut current_alpha = Num::Constant(E::Fr::one());
    powers_of_alpha_for_gates.push(current_alpha);
    for _ in 1..total_powers_of_alpha_for_gates {
        current_alpha = current_alpha.mul(cs, &alpha)?;
        powers_of_alpha_for_gates.push(current_alpha);
    }

    let copy_grand_product_alphas = {
        current_alpha = current_alpha.mul(cs, &alpha)?;
        let alpha_0 = current_alpha;

        current_alpha = current_alpha.mul(cs, &alpha)?;
        let alpha_1 = current_alpha;

        [alpha_0, alpha_1]
    };

    let lookup_grand_product_alphas = {
        current_alpha = current_alpha.mul(cs, &alpha)?;
        let alpha_0 = current_alpha;

        current_alpha = current_alpha.mul(cs, &alpha)?;
        let alpha_1 = current_alpha;

        current_alpha = current_alpha.mul(cs, &alpha)?;
        let alpha_2 = current_alpha;

        [alpha_0, alpha_1, alpha_2]
    };

    for commitment in proof.quotient_poly_parts_commitments.iter() {
        transcript.commit_point(cs, commitment)?;
    }

    let z = transcript.get_challenge(cs)?;
    let z_omega = z.mul(cs, &vk.omega)?;

    let (z_in_domain_size, z_omega_in_domain_size) = {
        let absolute_limit = (E::Fr::S + 1) as usize;
        let mut pow_decomposition = vk
            .n_next_power_of_two
            .get_variable()
            .into_bits_le(cs, Some(absolute_limit))?;
        // make MSB first
        pow_decomposition.reverse();

        let z = z.get_variable();
        let z_in_pow_domain_size = AllocatedNum::<E>::pow(cs, &z, &pow_decomposition)?;

        let z_omega = z_omega.get_variable();
        let z_omega_in_pow_domain_size = AllocatedNum::<E>::pow(cs, &z_omega, &pow_decomposition)?;

        (
            Num::Variable(z_in_pow_domain_size),
            Num::Variable(z_omega_in_pow_domain_size),
        )
    };

    let quotient_at_z = proof.quotient_poly_opening_at_z.clone();
    transcript.commit_scalar(cs, quotient_at_z)?;

    let mut all_values_queried_at_z = vec![];
    let mut all_values_queried_at_z_omega = vec![];

    let mut all_commitments_queried_at_z = vec![];
    let mut all_commitments_queried_at_z_omega = vec![];

    // commit openings of state polys
    for (s, c) in proof
        .state_polys_openings_at_z
        .iter()
        .zip(proof.state_polys_commitments.iter())
    {
        transcript.commit_scalar(cs, s.clone())?;

        all_values_queried_at_z.push(s.clone());
        all_commitments_queried_at_z.push(c.clone());
    }

    {
        let s = &proof.state_polys_openings_at_dilations[0];
        let c = &proof.state_polys_commitments[3];

        transcript.commit_scalar(cs, s.clone())?;

        all_values_queried_at_z_omega.push(s.clone());
        all_commitments_queried_at_z_omega.push(c.clone());
    }

    let mut selector_values = vec![];
    assert_eq!(
        geometry.gate_selectors_openings_at_z_locations.len(),
        proof.gate_selectors_openings_at_z.len()
    );
    assert_eq!(proof.gate_selectors_openings_at_z.len(), 1);
    for &idx in geometry.gate_selectors_openings_at_z_locations.iter() {
        assert_eq!(idx, 0);
        let s = &proof.gate_selectors_openings_at_z[idx];
        let c = &vk.gate_selectors_commitments[idx];

        transcript.commit_scalar(cs, s.clone())?;

        selector_values.push(s.clone());
        all_values_queried_at_z.push(s.clone());
        all_commitments_queried_at_z.push(c.clone());
    }

    // copy-permutation polynomials queries

    let mut copy_permutation_polys_openings_at_z_iter =
        proof.copy_permutation_polys_openings_at_z.iter();

    assert_eq!(vk.permutation_commitments.len(), geometry.num_state_polys);
    let mut copy_permutation_polys_commitments_iter = vk.permutation_commitments.iter();

    let mut copy_permutation_queries = vec![];

    for _ in 0..(geometry.num_state_polys - 1) {
        let value = copy_permutation_polys_openings_at_z_iter
            .next()
            .ok_or(SynthesisError::AssignmentMissing)?;

        transcript.commit_scalar(cs, value.clone())?;

        copy_permutation_queries.push(value.clone());
        all_values_queried_at_z.push(value.clone());

        let commitment = copy_permutation_polys_commitments_iter
            .next()
            .ok_or(SynthesisError::AssignmentMissing)?;
        all_commitments_queried_at_z.push(commitment.clone());
    }

    assert!(copy_permutation_polys_openings_at_z_iter.next().is_none());

    // copy-permutation grand product query

    // for polys below we will insert queried commitments manually into the corresponding lists
    let copy_permutation_z_at_z_omega = proof.copy_permutation_grand_product_opening_at_z_omega;
    transcript.commit_scalar(cs, copy_permutation_z_at_z_omega)?;

    transcript.commit_scalar(cs, proof.lookup_t_poly_opening_at_z)?;
    transcript.commit_scalar(cs, proof.lookup_selector_poly_opening_at_z)?;
    transcript.commit_scalar(cs, proof.lookup_table_type_poly_opening_at_z)?;

    // now at z*omega
    transcript.commit_scalar(cs, proof.lookup_s_poly_opening_at_z_omega)?;
    transcript.commit_scalar(cs, proof.lookup_grand_product_opening_at_z_omega)?;
    transcript.commit_scalar(cs, proof.lookup_t_poly_opening_at_z_omega)?;

    let linearization_at_z = proof.linearization_poly_opening_at_z;
    transcript.commit_scalar(cs, linearization_at_z)?;

    let omega_inv = Num::Variable(vk.omega.get_variable().inverse(cs)?);

    let l_0_at_z = evaluate_lagrange_poly_for_variable_domain_size(
        cs,
        0,
        vk.n_next_power_of_two.get_variable(),
        &omega_inv.get_variable(),
        z.get_variable(),
        z_in_domain_size.get_variable(),
    )?;

    let l_0_at_z = Num::Variable(l_0_at_z);

    // L_1(z*omega) = L_0(z), so L_0(z*omega) = L_{n-1}(z)
    let l_n_minus_one_at_z = evaluate_lagrange_poly_for_variable_domain_size(
        cs,
        0,
        vk.n_next_power_of_two.get_variable(),
        &omega_inv.get_variable(),
        z_omega.get_variable(),
        z_omega_in_domain_size.get_variable(),
    )?;

    let l_n_minus_one_at_z = Num::Variable(l_n_minus_one_at_z);

    let mut lhs = proof.quotient_poly_opening_at_z.clone();
    let vanishing_at_z = Num::Variable(evaluate_vanishing_poly(
        cs,
        z_in_domain_size.get_variable(),
    )?);
    lhs = lhs.mul(cs, &vanishing_at_z)?;

    let mut t_num_on_full_domain = proof.linearization_poly_opening_at_z.clone();
    // add inputs (only one)
    {
        let input = &proof.inputs[0];
        let mut inputs_term = l_0_at_z.mul(cs, &input)?;

        let selector_value = selector_values[0];
        inputs_term = inputs_term.mul(cs, &selector_value)?;

        t_num_on_full_domain = t_num_on_full_domain.add(cs, &inputs_term)?;
    }

    // now aggregate leftovers from grand product for copy permutation
    {
        // - alpha_0 * (a + perm(z) * beta + gamma)*()*(d + gamma) * z(z*omega)
        let [alpha_0, alpha_1] = copy_grand_product_alphas;

        let mut factor = alpha_0;
        factor = factor.mul(cs, &copy_permutation_z_at_z_omega)?;

        for idx in 0..(geometry.num_state_polys - 1) {
            let wire_value = &proof.state_polys_openings_at_z[idx];
            let permutation_at_z = copy_permutation_queries[idx];

            let mut t = permutation_at_z;

            t = t.mul(cs, &beta_for_copy_permutation)?;
            t = t.add(cs, &wire_value)?;
            t = t.add(cs, &gamma_for_copy_permutation)?;

            factor = factor.mul(cs, &t)?;
        }

        let mut tmp = proof.state_polys_openings_at_z[geometry.num_state_polys - 1].clone();
        tmp = tmp.add(cs, &gamma_for_copy_permutation)?;

        factor = factor.mul(cs, &tmp)?;

        t_num_on_full_domain = t_num_on_full_domain.sub(cs, &factor)?;

        // - L_0(z) * alpha_1

        let tmp = l_0_at_z.mul(cs, &alpha_1)?;
        t_num_on_full_domain = t_num_on_full_domain.sub(cs, &tmp)?;
    }

    struct AllocatedLookupQuery<E: Engine> {
        s_at_z_omega: Num<E>,
        grand_product_at_z_omega: Num<E>,
        t_at_z: Num<E>,
        t_at_z_omega: Num<E>,
        selector_at_z: Num<E>,
        table_type_at_z: Num<E>,
        beta_plus_one: Num<E>,
        gamma_beta: Num<E>,
    }

    // and if exists - grand product for lookup permutation
    let lookup_query = {
        let [alpha_0, alpha_1, alpha_2] = lookup_grand_product_alphas;

        let beta_for_lookup_permutation = beta_for_lookup;
        let gamma_for_lookup_permutation = gamma_for_lookup;
        let beta_plus_one = beta_for_lookup_permutation.add(cs, &Num::Constant(E::Fr::one()))?;
        let gamma_beta = gamma_for_lookup_permutation.mul(cs, &beta_plus_one)?;

        let absolute_limit = (E::Fr::S + 1) as usize;
        let domain_size_minus_one = vk
            .n_next_power_of_two
            .sub(cs, &Num::Constant(E::Fr::one()))?;
        let mut pow_decomposition = domain_size_minus_one
            .get_variable()
            .into_bits_le(cs, Some(absolute_limit))?;
        // make MSB first
        pow_decomposition.reverse();

        let expected = AllocatedNum::<E>::pow(cs, &gamma_beta.get_variable(), &pow_decomposition)?;
        let expected = Num::Variable(expected);

        let lookup_queries = AllocatedLookupQuery::<E> {
            s_at_z_omega: proof.lookup_s_poly_opening_at_z_omega,
            grand_product_at_z_omega: proof.lookup_grand_product_opening_at_z_omega,
            t_at_z: proof.lookup_t_poly_opening_at_z,
            t_at_z_omega: proof.lookup_t_poly_opening_at_z_omega,
            selector_at_z: proof.lookup_selector_poly_opening_at_z,
            table_type_at_z: proof.lookup_table_type_poly_opening_at_z,
            beta_plus_one: beta_plus_one,
            gamma_beta: gamma_beta,
        };

        // in a linearization we've taken terms:
        // - s(x) from the alpha_0 * Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))
        // - and Z(x) from - alpha_0 * Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) (term in full) +
        // + alpha_1 * (Z(x) - 1) * L_{0}(z) + alpha_2 * (Z(x) - expected) * L_{n-1}(z)

        // first make alpha_0 * Z(x*omega)*(\gamma*(1 + \beta) + \beta * s(x*omega)))

        let mut tmp = lookup_queries.s_at_z_omega;
        tmp = tmp.mul(cs, &beta_for_lookup_permutation)?;
        tmp = tmp.add(cs, &gamma_beta)?;
        tmp = tmp.mul(cs, &lookup_queries.grand_product_at_z_omega)?;
        tmp = tmp.mul(cs, &alpha_0)?;

        // (z - omega^{n-1}) for this part
        let omega_var = vk.omega.get_variable();
        let last_omega = AllocatedNum::<E>::pow(cs, &omega_var, &pow_decomposition)?;
        let z_minus_last_omega = z.sub(cs, &Num::Variable(last_omega))?;

        tmp = tmp.mul(cs, &z_minus_last_omega)?;

        t_num_on_full_domain = t_num_on_full_domain.add(cs, &tmp)?;

        // // - alpha_1 * L_{0}(z)

        let tmp = l_0_at_z.mul(cs, &alpha_1)?;

        t_num_on_full_domain = t_num_on_full_domain.sub(cs, &tmp)?;

        // // - alpha_2 * expected L_{n-1}(z)

        let mut tmp = l_n_minus_one_at_z;
        tmp = tmp.mul(cs, &expected)?;
        tmp = tmp.mul(cs, &alpha_2)?;

        t_num_on_full_domain = t_num_on_full_domain.sub(cs, &tmp)?;

        lookup_queries
    };

    let rhs = t_num_on_full_domain;

    let valid = Num::equals(cs, &lhs, &rhs)?;

    // now we need to reconstruct the effective linearization poly with homomorphic properties
    let linearization_commitment_parts = {
        let mut parts = vec![];

        let mut challenges_slice = &powers_of_alpha_for_gates[..];
        let num_challenges = 1; // main gate has 1 term
        let (for_gate, rest) = challenges_slice.split_at(num_challenges);
        challenges_slice = rest;

        assert_eq!(for_gate.len(), 1);

        // main gate linearizes over selectors and then multiplied by the selector value

        // linear terms
        for (val, sel) in proof
            .state_polys_openings_at_z
            .iter()
            .zip(vk.gate_setup_commitments[..4].iter())
        {
            parts.push((val.clone(), sel.clone()));
        }

        let mut setup_poly_idx = 4;

        // multiplication
        let q_m = &vk.gate_setup_commitments[setup_poly_idx];
        let tmp =
            proof.state_polys_openings_at_z[0].mul(cs, &proof.state_polys_openings_at_z[1])?;
        parts.push((tmp, q_m.clone()));
        setup_poly_idx += 1;

        if USE_MODIFIED_MAIN_GATE {
            // biquadratic gate part 2
            let q_m_ac = &vk.gate_setup_commitments[setup_poly_idx];
            let tmp =
                proof.state_polys_openings_at_z[0].mul(cs, &proof.state_polys_openings_at_z[2])?;
            parts.push((tmp, q_m_ac.clone()));
            setup_poly_idx += 1;
        }

        // constant
        let q_const = &vk.gate_setup_commitments[setup_poly_idx];
        let one = Num::Variable(AllocatedNum::one(cs));
        parts.push((one, q_const.clone()));
        setup_poly_idx += 1;

        // D_next
        let q_d_next = &vk.gate_setup_commitments[setup_poly_idx];
        parts.push((
            proof.state_polys_openings_at_dilations[0].clone(),
            q_d_next.clone(),
        ));
        setup_poly_idx += 1;

        assert_eq!(setup_poly_idx, geometry.total_num_gate_setup_polys);

        // mul by gate selector and challenge
        let gate_selector = &proof.gate_selectors_openings_at_z[0].mul(cs, &for_gate[0])?;

        for pair in parts.iter_mut() {
            let tmp = pair.0.mul(cs, &gate_selector)?;
            pair.0 = tmp;
        }

        assert_eq!(challenges_slice.len(), 3);
        let (challenges, _) = challenges_slice.split_at(3);

        // non-linearity gate
        let a_value = &proof.state_polys_openings_at_z[0];
        let b_value = &proof.state_polys_openings_at_z[1];
        let c_value = &proof.state_polys_openings_at_z[2];
        let d_value = &proof.state_polys_openings_at_z[3];

        // a^2 - b = 0
        let mut result = a_value.clone();
        result = result.mul(cs, &result)?;
        result = result.sub(cs, &b_value)?;
        result = result.mul(cs, &challenges[0])?;

        // b^2 - c = 0
        let mut tmp = b_value.clone();
        tmp = tmp.mul(cs, &tmp)?;
        tmp = tmp.sub(cs, &c_value)?;
        tmp = tmp.mul(cs, &challenges[1])?;

        result = result.add(cs, &tmp)?;

        // c*a - d = 0;
        let mut tmp = c_value.clone();
        tmp = tmp.mul(cs, &a_value)?;
        tmp = tmp.sub(cs, &d_value)?;
        tmp = tmp.mul(cs, &challenges[2])?;

        result = result.add(cs, &tmp)?;

        // multiply this by the gate selector
        parts.push((result, vk.gate_selectors_commitments[1].clone()));

        // add contributions from copy-permutation and lookup-permutation

        // copy-permutation linearization comtribution
        {
            // + (a(z) + beta*z + gamma)*()*()*()*Z(x)

            let [alpha_0, alpha_1] = copy_grand_product_alphas;

            let some_one = Some(Num::Constant(E::Fr::one()));
            let mut non_residues_iterator = some_one.iter().chain(&vk.non_residues);

            let mut factor = alpha_0;

            for idx in 0..geometry.num_state_polys {
                let wire_value = proof.state_polys_openings_at_z[idx].clone();
                let mut t = z;
                let non_res = non_residues_iterator.next().unwrap();
                t = t.mul(cs, &non_res)?;
                t = t.mul(cs, &beta_for_copy_permutation)?;
                t = t.add(cs, &wire_value)?;
                t = t.add(cs, &gamma_for_copy_permutation)?;

                factor = factor.mul(cs, &t)?;
            }

            assert!(non_residues_iterator.next().is_none());

            // add into commitment
            parts.push((
                factor,
                proof.copy_permutation_grand_product_commitment.clone(),
            ));

            // - (a(z) + beta*perm_a + gamma)*()*()*z(z*omega) * beta * perm_d(X)

            let mut factor = alpha_0;
            factor = factor.mul(cs, &beta_for_copy_permutation)?;
            factor = factor.mul(cs, &copy_permutation_z_at_z_omega)?;

            for idx in 0..(geometry.num_state_polys - 1) {
                let wire_value = proof.state_polys_openings_at_z[idx].clone();
                let permutation_at_z = copy_permutation_queries[idx];
                let mut t = permutation_at_z;

                t = t.mul(cs, &beta_for_copy_permutation)?;
                t = t.add(cs, &wire_value)?;
                t = t.add(cs, &gamma_for_copy_permutation)?;

                factor = factor.mul(cs, &t)?;
            }

            // Don't forget to negate
            factor = factor.negate(cs)?;

            // add into commitment
            parts.push((
                factor,
                vk.permutation_commitments[geometry.num_state_polys - 1].clone(),
            ));

            // + L_0(z) * Z(x)

            let factor = l_0_at_z.mul(cs, &alpha_1)?;

            // and IMPORTANT part here: we use multiexp with window size at most 4,
            // and we need to compute combinations P0 +- P1 +- P2 +- P3 in there

            // But if we add a committment here then we will deterministically have equal points over the window of 4
            // so we reshuffle, and it doesn't affect as we don't care about particular order of the set for MSM

            let mut tmp = vec![(
                factor,
                proof.copy_permutation_grand_product_commitment.clone(),
            )];
            let p = std::mem::replace(&mut parts, vec![]);
            tmp.extend(p);

            parts = tmp;
        }

        // lookup grand product linearization

        // due to separate divisor it's not obvious if this is beneficial without some tricks
        // like multiplication by (1 - L_{n-1}) or by (x - omega^{n-1})

        // Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) -
        // Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) == 0
        // check that (Z(x) - 1) * L_{0} == 0
        // check that (Z(x) - expected) * L_{n-1} == 0, or (Z(x*omega) - expected)* L_{n-2} == 0

        // f(x) does not need to be opened as it's made of table selector and witnesses
        // if we pursue the strategy from the linearization of a copy-permutation argument
        // then we leave something like s(x) from the Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) term,
        // and Z(x) from Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) term,
        // with terms with lagrange polys as multipliers left intact

        {
            let [alpha_0, alpha_1, alpha_2] = lookup_grand_product_alphas;

            let lookup_queries = lookup_query;

            // let s_at_z_omega = lookup_queries.s_at_z_omega;
            let grand_product_at_z_omega = lookup_queries.grand_product_at_z_omega;
            let t_at_z = lookup_queries.t_at_z;
            let t_at_z_omega = lookup_queries.t_at_z_omega;
            let selector_at_z = lookup_queries.selector_at_z;
            let table_type_at_z = lookup_queries.table_type_at_z;

            let beta_for_lookup_permutation = beta_for_lookup;
            let gamma_for_lookup_permutation = gamma_for_lookup;

            let beta_plus_one = lookup_queries.beta_plus_one;
            let gamma_beta = lookup_queries.gamma_beta;

            // (Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) -
            // Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)))*(X - omega^{n-1})

            let last_omega = omega_inv;
            let z_minus_last_omega = z.sub(cs, &last_omega)?;

            // s(x) from the Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))
            let mut factor = grand_product_at_z_omega; // we do not need to account for additive terms
            factor = factor.mul(cs, &alpha_0)?;
            factor = factor.mul(cs, &z_minus_last_omega)?;

            // add into commitment
            parts.push((factor, proof.lookup_s_poly_commitment.clone()));

            // Z(x) from - alpha_0 * Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega))
            // + alpha_1 * Z(x) * L_{0}(z) + alpha_2 * Z(x) * L_{n-1}(z)

            // accumulate coefficient
            let mut factor = t_at_z_omega;
            factor = factor.mul(cs, &beta_for_lookup_permutation)?;
            factor = factor.add(cs, &t_at_z)?;
            factor = factor.add(cs, &gamma_beta)?;

            // (\gamma + f(x))

            let mut f_reconstructed = Num::Constant(E::Fr::zero());
            let mut current = Num::Constant(E::Fr::one());
            let eta = eta;
            // a,b,c
            assert_eq!(
                geometry.num_state_polys, 4,
                "lookup is only defined if state width is 4"
            );
            for idx in 0..(geometry.num_state_polys - 1) {
                let mut value = proof.state_polys_openings_at_z[idx];

                value = value.mul(cs, &current)?;
                f_reconstructed = f_reconstructed.add(cs, &value)?;

                current = current.mul(cs, &eta)?;
            }

            // and table type
            let mut t = table_type_at_z;
            t = t.mul(cs, &current)?;
            f_reconstructed = f_reconstructed.add(cs, &t)?;

            f_reconstructed = f_reconstructed.mul(cs, &selector_at_z)?;
            f_reconstructed = f_reconstructed.add(cs, &gamma_for_lookup_permutation)?;

            // end of (\gamma + f(x)) part

            factor = factor.mul(cs, &f_reconstructed)?;
            factor = factor.mul(cs, &beta_plus_one)?;
            factor = Num::Constant(E::Fr::zero()).sub(cs, &factor)?; // don't forget minus sign
            factor = factor.mul(cs, &alpha_0)?;

            // Multiply by (z - omega^{n-1})

            factor = factor.mul(cs, &z_minus_last_omega)?;

            // L_{0}(z) in front of Z(x)

            let mut tmp = l_0_at_z;
            tmp = tmp.mul(cs, &alpha_1)?;
            factor = factor.add(cs, &tmp)?;

            // L_{n-1}(z) in front of Z(x)

            let mut tmp = l_n_minus_one_at_z;
            tmp = tmp.mul(cs, &alpha_2)?;
            factor = factor.add(cs, &tmp)?;

            // add into commitment
            parts.push((factor, proof.lookup_grand_product_commitment.clone()));
        }

        parts
    };

    let v = transcript.get_challenge(cs)?;

    // commit proofs

    transcript.commit_point(cs, &proof.opening_proof_at_z)?;
    transcript.commit_point(cs, &proof.opening_proof_at_z_omega)?;

    let u = transcript.get_challenge(cs)?;

    // first perform naive verification at z
    // f(x) - f(z) = q(x)(x - z) =>
    // e(f(x) - f(z)*g + z*q(x), h)*e(-q(x), h^x) == 1
    // when we aggregate we need to aggregate f(x) part (commitments) and f(z) part (values)

    // create multiopening that takes care about delinearization using v, and also uses external global delinearization factor
    let mut multiopening_at_z = MultiOpening::new_at_point(
        cs,
        &z.get_variable(),
        v.get_variable(),
        Some(multiopening_delinearization_challenge.get_variable()),
    )?;

    // quotient at Z

    let quotient_commitment_aggregated = {
        let mut result = vec![];
        let mut quotient_commitments_iter = proof.quotient_poly_parts_commitments.iter();

        let mut current = Num::Variable(AllocatedNum::one(cs));

        result.push((
            current.clone(),
            quotient_commitments_iter.next().unwrap().clone(),
        ));
        for part in quotient_commitments_iter {
            current = current.mul(cs, &z_in_domain_size)?;
            let tmp = part.clone();

            result.push((current, tmp));
        }

        result
    };

    // start with quotient at z

    let (quotient_at_z, quotient_commitment_aggregated) = mask_virtual_commitment_with_value(
        cs,
        &valid,
        quotient_at_z,
        quotient_commitment_aggregated,
    )?;

    multiopening_at_z.add_single_virtual_commitment(
        cs,
        &quotient_commitment_aggregated,
        quotient_at_z,
    )?;

    // linearization at z
    let (linearization_at_z, linearization_commitment_parts) = mask_virtual_commitment_with_value(
        cs,
        &valid,
        linearization_at_z,
        linearization_commitment_parts,
    )?;

    multiopening_at_z.add_single_virtual_commitment(
        cs,
        &linearization_commitment_parts,
        linearization_at_z,
    )?;

    for (val, comm) in all_values_queried_at_z
        .into_iter()
        .zip(all_commitments_queried_at_z.into_iter())
    {
        let (val, comm) = mask_commitment(cs, &valid, (val, comm))?;
        multiopening_at_z.add_raw_commitment(cs, &comm, val)?;
    }

    let reconstructed_lookup_t_poly_commitment = {
        let mut result = vec![];

        let mut commitments_iter = vk.lookup_tables_commitments.iter();

        let mut current = Num::Variable(AllocatedNum::one(cs));

        let next = commitments_iter.next().unwrap().clone();
        result.push((current.clone(), next));
        for part in commitments_iter {
            current = current.mul(cs, &eta)?;
            let tmp = part.clone();
            result.push((current, tmp));
        }

        result
    };

    let (lookup_t_poly_opening_at_z, reconstructed_lookup_t_poly_commitment) =
        mask_virtual_commitment_with_value(
            cs,
            &valid,
            proof.lookup_t_poly_opening_at_z.clone(),
            reconstructed_lookup_t_poly_commitment,
        )?;

    multiopening_at_z.add_single_virtual_commitment(
        cs,
        &reconstructed_lookup_t_poly_commitment,
        lookup_t_poly_opening_at_z,
    )?;

    let (lookup_selector_poly_opening_at_z, lookup_selector_commitment) = mask_commitment(
        cs,
        &valid,
        (
            proof.lookup_selector_poly_opening_at_z.clone(),
            vk.lookup_selector_commitment.clone(),
        ),
    )?;

    multiopening_at_z.add_raw_commitment(
        cs,
        &lookup_selector_commitment,
        lookup_selector_poly_opening_at_z,
    )?;

    let (lookup_table_type_poly_opening_at_z, lookup_table_type_commitment) = mask_commitment(
        cs,
        &valid,
        (
            proof.lookup_table_type_poly_opening_at_z.clone(),
            vk.lookup_table_type_commitment.clone(),
        ),
    )?;

    multiopening_at_z.add_raw_commitment(
        cs,
        &lookup_table_type_commitment,
        lookup_table_type_poly_opening_at_z,
    )?;

    // now create multiopening at z*omega by first pulling the v power from the openins at z

    // NOTE: it has multiopening_delinearization_challenge internally!
    let v_power = multiopening_at_z.next_factor.clone();

    // create initial factor as v^n * u * external_delin
    let factor = v_power.mul(cs, &u)?;

    let mut multiopening_at_z_omega = MultiOpening::new_at_point(
        cs,
        &z_omega.get_variable(),
        v.get_variable(),
        Some(factor.get_variable()),
    )?;

    // copy Z(z*omega)
    let (copy_permutation_z_at_z_omega, copy_permutation_grand_product_commitment) =
        mask_commitment(
            cs,
            &valid,
            (
                proof
                    .copy_permutation_grand_product_opening_at_z_omega
                    .clone(),
                proof.copy_permutation_grand_product_commitment.clone(),
            ),
        )?;

    multiopening_at_z_omega.add_raw_commitment(
        cs,
        &copy_permutation_grand_product_commitment,
        copy_permutation_z_at_z_omega,
    )?;

    for (val, comm) in all_values_queried_at_z_omega
        .into_iter()
        .zip(all_commitments_queried_at_z_omega.into_iter())
    {
        let (val, comm) = mask_commitment(cs, &valid, (val, comm))?;
        multiopening_at_z_omega.add_raw_commitment(cs, &comm, val)?;
    }

    // Lookup S(z*omega)
    let (lookup_s_poly_opening_at_z_omega, lookup_s_poly_commitment) = mask_commitment(
        cs,
        &valid,
        (
            proof.lookup_s_poly_opening_at_z_omega.clone(),
            proof.lookup_s_poly_commitment.clone(),
        ),
    )?;

    multiopening_at_z_omega.add_raw_commitment(
        cs,
        &lookup_s_poly_commitment,
        lookup_s_poly_opening_at_z_omega,
    )?;

    // Lookup Z(z*omega)
    let (lookup_grand_product_opening_at_z_omega, lookup_grand_product_commitment) =
        mask_commitment(
            cs,
            &valid,
            (
                proof.lookup_grand_product_opening_at_z_omega.clone(),
                proof.lookup_grand_product_commitment.clone(),
            ),
        )?;

    multiopening_at_z_omega.add_raw_commitment(
        cs,
        &lookup_grand_product_commitment,
        lookup_grand_product_opening_at_z_omega,
    )?;

    // Lookup T(z*omega)
    let lookup_t_poly_opening_at_z_omega =
        mask_scalar(cs, &valid, proof.lookup_t_poly_opening_at_z_omega.clone())?;
    multiopening_at_z_omega.add_single_virtual_commitment(
        cs,
        &reconstructed_lookup_t_poly_commitment,
        lookup_t_poly_opening_at_z_omega,
    )?;

    let (_, accumulated_value_at_z) = multiopening_at_z
        .add_into_partial_accumulator_and_split_scalars(
            cs,
            partial_accumulator_pair_with_generator,
        )?;
    let (_, accumulated_value_at_z_omega) = multiopening_at_z_omega
        .add_into_partial_accumulator_and_split_scalars(
            cs,
            partial_accumulator_pair_with_generator,
        )?;

    // something like
    // \sum_{i} v^i * (f_{i}(x) - f_{i}(z))/(x - z) = q(x)

    // we also multiply it externally by some delin

    // partial accumulator contains delin * \sum v^{i} * f(x)

    // - delin (\sum v^{i} * f(z)) * g (delin comes from the accumulator itself)
    let mut scalar_for_generator =
        Num::Variable(accumulated_value_at_z.add(cs, &accumulated_value_at_z_omega)?);
    scalar_for_generator = scalar_for_generator.negate(cs)?;
    // mask it if proof is invalid, so we have commitments to zero everywhere
    scalar_for_generator = Num::conditionally_select(
        cs,
        &valid,
        &scalar_for_generator,
        &Num::Constant(E::Fr::zero()),
    )?;

    // add parts like + delin * z * q(x) for pairing with generator
    // here we do not need masking as q(x) can be zero here
    let scalar_for_pair_at_z = z.mul(cs, multiopening_delinearization_challenge)?;
    let mut scalar_for_pair_at_z_omega = z_omega.mul(cs, multiopening_delinearization_challenge)?;
    scalar_for_pair_at_z_omega = scalar_for_pair_at_z_omega.mul(cs, &u)?;

    // mask q(x) parts if proof is valid, so we do not have to do it outside
    let opening_proof_at_z = mask_point(cs, &valid, proof.opening_proof_at_z.clone())?;
    let opening_proof_at_z_omega = mask_point(cs, &valid, proof.opening_proof_at_z_omega.clone())?;

    let pair = (scalar_for_pair_at_z, opening_proof_at_z.clone());
    pair.accumulate_into(cs, partial_accumulator_pair_with_generator)?;

    let pair = (scalar_for_pair_at_z_omega, opening_proof_at_z_omega.clone());
    pair.accumulate_into(cs, partial_accumulator_pair_with_generator)?;

    // add into pairing with g^x (with negation here!)
    let scalar_for_pair_at_z = multiopening_delinearization_challenge.negate(cs)?;
    let mut scalar_for_pair_at_z_omega = u.mul(cs, multiopening_delinearization_challenge)?;
    scalar_for_pair_at_z_omega = scalar_for_pair_at_z_omega.negate(cs)?;

    let pair = (scalar_for_pair_at_z, opening_proof_at_z);
    pair.accumulate_into(cs, partial_accumulator_pair_with_x)?;

    let pair = (scalar_for_pair_at_z_omega, opening_proof_at_z_omega);
    pair.accumulate_into(cs, partial_accumulator_pair_with_x)?;

    Ok((valid, scalar_for_generator))
}

// #[cfg(test)]
// pub(crate) mod test {
//     use super::*;
//     use rescue_poseidon::HashParams;
//     use rescue_poseidon::{RescueParams, CircuitGenericSponge, CustomGate};
//     use crate::utils::{AWIDTH_VALUE, SWIDTH_VALUE};

//     #[derive(Derivative)]
//     #[derivative(Clone, Debug)]
//     pub struct TesterCircuitForReferenceGeometry<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> {
//         params: P,
//         _m: std::marker::PhantomData<E>,
//     }

//     impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> Circuit<E> for TesterCircuitForReferenceGeometry<E, P, AWIDTH, SWIDTH>
//     {
//         type MainGate = Width4MainGateWithDNext;
//         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//             let dummy = CS::get_dummy_variable();

//             // need to create a table (any)
//             let columns = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
//             let range_table = LookupTableApplication::new_range_table_of_width_3(2, columns.clone())?;
//             let range_table_name = range_table.functional_name();

//             let xor_table = LookupTableApplication::new_xor_table(2, columns.clone())?;
//             let xor_table_name = xor_table.functional_name();

//             let and_table = LookupTableApplication::new_and_table(2, columns)?;
//             let and_table_name = and_table.functional_name();

//             cs.add_table(range_table)?;
//             cs.add_table(xor_table)?;
//             cs.add_table(and_table)?;

//             let binary_x_value = E::Fr::from_str("3").unwrap();
//             let binary_y_value = E::Fr::from_str("1").unwrap();

//             let t = AllocatedNum::zero(cs);
//             let tt = AllocatedNum::one(cs);
//             let ttt = t.mul(cs, &tt)?;
//             ttt.inputize(cs)?;

//             let binary_x = cs.alloc(|| {
//                 Ok(binary_x_value)
//             })?;

//             let binary_y = cs.alloc(|| {
//                 Ok(binary_y_value)
//             })?;

//             {
//                 let table = cs.get_table(&and_table_name)?;
//                 let num_keys_and_values = table.width();

//                 let and_result_value = table.query(&[binary_x_value, binary_y_value])?[0];

//                 let binary_z = cs.alloc(|| {
//                     Ok(and_result_value)
//                 })?;

//                 cs.begin_gates_batch_for_step()?;

//                 let vars = [binary_x, binary_y, binary_z, dummy];
//                 cs.allocate_variables_without_gate(
//                     &vars,
//                     &[]
//                 )?;

//                 cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

//                 cs.end_gates_batch_for_step()?;
//             }

//             // and use rescue
//             let el = Num::Variable(AllocatedNum::one(cs));
//             let _ = CircuitGenericSponge::hash(cs, &[el], &self.params, None)?;

//             // and pad to not have zeroes anywhere
//             let zero_var = cs.alloc(|| {
//                 Ok(E::Fr::zero())
//             })?;

//             let one_var = cs.alloc(|| {
//                 Ok(E::Fr::one())
//             })?;

//             let zero = E::Fr::zero();
//             let one = E::Fr::one();

//             let mut negative_one = one;
//             negative_one.negate();
//             let mut two = one;
//             two.double();

//             let mg = CS::MainGate::default();
//             let gate_term = MainGateTerm::new();

//             // 2c - 1 - d_next = 0
//             let (mut vars, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
//             vars[2] = one_var;

//             // C
//             gate_coefs[2] = two;
//             // constant
//             gate_coefs[5] = negative_one;
//             // D_next
//             gate_coefs[6] = negative_one;

//             cs.begin_gates_batch_for_step()?;
//             cs.new_gate_in_batch(
//                 &mg,
//                 &gate_coefs,
//                 &vars,
//                 &[]
//             )?;

//             cs.end_gates_batch_for_step()?;

//             // 0*d = 0
//             let gate_term = MainGateTerm::new();
//             let (mut vars, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
//             vars[3] = one_var;

//             cs.begin_gates_batch_for_step()?;
//             cs.new_gate_in_batch(
//                 &mg,
//                 &gate_coefs,
//                 &vars,
//                 &[]
//             )?;

//             cs.end_gates_batch_for_step()?;

//             Ok(())
//         }
//         fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
//             Ok(
//                 vec![
//                     Self::MainGate::default().into_internal(),
//                     Rescue5CustomGate::default().into_internal(),
//                 ]
//             )
//         }
//     }

//     use crate::testing::create_test_artifacts;
//     use super::*;
//     use crate::ff::*;
//     use rand::{XorShiftRng, SeedableRng, Rng};
//     use crate::traits::*;
//     use crate::bellman::plonk::better_better_cs::cs::*;
//     use crate::data_structures::alg_binary_tree::rescue_impl::StaticGenericBinaryTreeHasher;
//     use crate::pairing::bn256::{Bn256, Fr, Fq, G1Affine};
//     use crate::bellman::worker::*;
//     use crate::bellman::kate_commitment::*;
//     use super::super::transcript::*;
//     use crate::bellman::plonk::better_better_cs::verifier::*;
//     use franklin_crypto::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;

//     pub(crate) fn create_vk_and_proof() -> (VerificationKey::<Bn256, CircuitWithNonlinearityAndLookups>, Proof::<Bn256, CircuitWithNonlinearityAndLookups>) {
//         let vk_file = std::fs::File::open("./vk.key");
//         let proof_file = std::fs::File::open("./proof.proof");
//         if vk_file.is_err() || proof_file.is_err() {
//             let (mut external_cs, _, _) = create_test_artifacts();

//             let params = bn254_rescue_params();

//             let mut params_with_custom_gates = params.clone();
//             params_with_custom_gates.use_custom_gate(CustomGate::QuinticWidth4);

//             let circuit = TesterCircuitForReferenceGeometry {
//                 params: params_with_custom_gates,
//                 _m: std::marker::PhantomData,
//             };

//             circuit.synthesize(&mut external_cs).unwrap();
//             external_cs.finalize();

//             let worker = Worker::new();

//             let crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(1024, &worker);

//             let setup = external_cs.create_setup::<TesterCircuitForReferenceGeometry<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(&worker).unwrap();
//             let vk = VerificationKey::from_setup(&setup, &worker, &crs).unwrap();

//             let rns_params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

//             let transcript_params = (&params, &rns_params);
//             let proof = external_cs.create_proof::<_, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(&worker, &setup, &crs, Some(transcript_params)).unwrap();

//             let valid = verify::<Bn256, TesterCircuitForReferenceGeometry<Bn256, _, AWIDTH_VALUE, SWIDTH_VALUE>, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//                 &vk,
//                 &proof,
//                 Some(transcript_params),
//             ).unwrap();

//             assert!(valid);

//             let mut vk_file = std::fs::File::create("./vk.key").unwrap();
//             vk.write(&mut vk_file).unwrap();

//             let mut proof_file = std::fs::File::create("./proof.proof").unwrap();
//             proof.write(&mut proof_file).unwrap();
//         }

//         let vk_file = std::fs::File::open("./vk.key").unwrap();
//         let proof_file = std::fs::File::open("./proof.proof").unwrap();

//         let vk = VerificationKey::<Bn256, CircuitWithNonlinearityAndLookups>::read(&vk_file).unwrap();
//         let proof = Proof::<Bn256, CircuitWithNonlinearityAndLookups>::read(&proof_file).unwrap();

//         (vk, proof)
//     }

//     pub(crate) fn get_g2_bases() -> Vec<crate::pairing::bn256::G2Affine> {
//         let worker = Worker::new();
//         let crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(32, &worker);

//         crs.g2_monomial_bases.as_slice().to_vec()
//     }

//     pub(crate) fn create_vk_and_proof_for_range_table_params(
//         rns_params: RnsParameters::<Bn256, Fq>,
//     ) -> (VerificationKey::<Bn256, CircuitWithNonlinearityAndLookups>, Proof::<Bn256, CircuitWithNonlinearityAndLookups>) {
//         let w = rns_params.range_check_info.optimal_multiple;
//         let vk_name_string = format!("./vk_{}.key", w);
//         let proof_name_string = format!("./proof_{}.proof", w);
//         let vk_name = &vk_name_string;
//         let proof_name = &proof_name_string;
//         let vk_file = std::fs::File::open(vk_name);
//         let proof_file = std::fs::File::open(proof_name);
//         if vk_file.is_err() || proof_file.is_err() {
//             let (mut external_cs, _, _) = create_test_artifacts();

//             let params = bn254_rescue_params();

//             let mut params_with_custom_gates = params.clone();
//             params_with_custom_gates.use_custom_gate(CustomGate::QuinticWidth4);

//             let circuit = TesterCircuitForReferenceGeometry {
//                 params: params_with_custom_gates,
//                 _m: std::marker::PhantomData,
//             };

//             circuit.synthesize(&mut external_cs).unwrap();
//             external_cs.finalize();

//             let worker = Worker::new();

//             let crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(1024, &worker);

//             let setup = external_cs.create_setup::<TesterCircuitForReferenceGeometry<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(&worker).unwrap();
//             let vk = VerificationKey::from_setup(&setup, &worker, &crs).unwrap();

//             let transcript_params = (&params, &rns_params);
//             let proof = external_cs.create_proof::<_, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(&worker, &setup, &crs, Some(transcript_params)).unwrap();
//             let valid = verify::<Bn256, TesterCircuitForReferenceGeometry<Bn256, _, AWIDTH_VALUE, SWIDTH_VALUE>, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//                 &vk,
//                 &proof,
//                 Some(transcript_params),
//             ).unwrap();

//             assert!(valid);

//             let mut vk_file = std::fs::File::create(vk_name).unwrap();
//             vk.write(&mut vk_file).unwrap();

//             let mut proof_file = std::fs::File::create(proof_name).unwrap();
//             proof.write(&mut proof_file).unwrap();
//         }

//         let vk_file = std::fs::File::open(vk_name).unwrap();
//         let proof_file = std::fs::File::open(proof_name).unwrap();

//         let vk = VerificationKey::<Bn256, CircuitWithNonlinearityAndLookups>::read(&vk_file).unwrap();
//         let proof = Proof::<Bn256, CircuitWithNonlinearityAndLookups>::read(&proof_file).unwrap();

//         (vk, proof)
//     }

//     #[test]
//     fn test_proof() {
//         let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         let params = bn254_rescue_params();
//         let rns_params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

//         let (mut cs, _, _) = create_test_artifacts();

//         let base_placeholder_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[0];

//         let some_random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[1];

//         let compensation_scalar: Fr = rng.gen();

//         let mut pair_with_gen_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let mut pair_with_x_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let (vk, proof) = create_vk_and_proof();

//         let transcript_params = (&params, &rns_params);
//         let valid = verify::<Bn256, _, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//             &vk,
//             &proof,
//             Some(transcript_params),
//         ).unwrap();

//         assert!(valid);

//         let ((pair_with_gen_value, pair_with_x_value), success) = aggregate::<Bn256, _, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//             &vk,
//             &proof,
//             Some(transcript_params),
//         ).unwrap();

//         assert!(success);

//         let p = ProofInRns {
//             proof: Some(proof),
//             rns_params: &rns_params,
//         };

//         let v = VkInRns {
//             vk: Some(vk),
//             rns_params: &rns_params,
//         };

//         let proof_witness: Vec<_> = p.encode().unwrap().into_iter().map(|el| Some(el)).collect();
//         let vk_witness: Vec<_> = v.encode().unwrap().into_iter().map(|el| Some(el)).collect();

//         let geometry = GeometryHint::hint_for_reference_geometry();

//         // let proof = AllocatedProof::from_witness_and_geometry(&mut cs, &proof_witness, &geometry, &rns_params).unwrap();
//         let vk = AllocatedVerificationKey::from_witness_and_geometry(&mut cs, &vk_witness, &geometry, &rns_params).unwrap();

//         let one = Num::Variable(AllocatedNum::one(&mut cs));

//         let zero_placeholder_point = PointAffine::zero(some_random_point, &rns_params);

//         let (valid, scalar) = aggregate_single_for_reference_geometry::<_, GenericTranscriptGadget<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>, _, false>(
//             &mut cs,
//             p,
//             &params,
//             &mut pair_with_gen_accumulator,
//             &mut pair_with_x_accumulator,
//             &vk,
//             &one,
//             &rns_params,
//         ).unwrap();

//         assert!(valid.get_value().unwrap());

//         let generator = PointAffine::constant(G1Affine::one(), &rns_params);
//         let generator = mask_point(&mut cs, &valid, generator).unwrap();

//         let pair = (scalar, generator);
//         pair.accumulate_into(&mut cs, &mut pair_with_gen_accumulator).unwrap();

//         println!("Accumulating to pair with generator");
//         dbg!(pair_with_gen_accumulator.multiexp_points.len());
//         let partial_with_gen = pair_with_gen_accumulator.finalize_completely(&mut cs).unwrap();
//         assert_eq!(partial_with_gen.get_value().unwrap(), pair_with_gen_value);
//         println!("Accumulating to pair with H^X");
//         dbg!(pair_with_x_accumulator.multiexp_points.len());
//         let partial_with_x = pair_with_x_accumulator.finalize_completely(&mut cs).unwrap();
//         assert_eq!(partial_with_x.get_value().unwrap(), pair_with_x_value);

//         println!("Aggregation of one proof with tables taken {} gates", cs.get_current_step_number());

//         println!("Checking if satisfied");
//         assert!(cs.is_satisfied());
//     }

//     #[test]
//     fn test_aggregate_invalid_proof() {
//         let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         let params = bn254_rescue_params();
//         let rns_params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

//         let (mut cs, _, _) = create_test_artifacts();

//         let base_placeholder_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[0];

//         let some_random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[1];

//         let compensation_scalar: Fr = rng.gen();

//         let mut pair_with_gen_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let mut pair_with_x_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let (vk, proof) = create_vk_and_proof();

//         let transcript_params = (&params, &rns_params);
//         let valid = verify::<Bn256, _, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//             &vk,
//             &proof,
//             Some(transcript_params),
//         ).unwrap();

//         assert!(valid);

//         // let ((pair_with_gen_value, pair_with_x_value), success) = aggregate::<Bn256, _, RescueTranscriptForRNSInFieldOnly<Bn256>>(
//         //     &vk,
//         //     &proof,
//         //     Some(transcript_params),
//         // ).unwrap();

//         // assert!(success);

//         // mess up with a proof
//         let mut proof = proof;
//         proof.quotient_poly_opening_at_z = Fr::one();
//         // do not touch opening elements
//         proof.opening_proof_at_z = G1Affine::zero();
//         proof.opening_proof_at_z_omega = G1Affine::zero();

//         let p = ProofInRns {
//             proof: Some(proof),
//             rns_params: &rns_params,
//         };

//         let v = VkInRns {
//             vk: Some(vk),
//             rns_params: &rns_params,
//         };

//         let proof_witness: Vec<_> = p.encode().unwrap().into_iter().map(|el| Some(el)).collect();
//         let vk_witness: Vec<_> = v.encode().unwrap().into_iter().map(|el| Some(el)).collect();

//         let geometry = GeometryHint::hint_for_reference_geometry();

//         // let proof = AllocatedProof::from_witness_and_geometry(&mut cs, &proof_witness, &geometry, &rns_params).unwrap();
//         let vk = AllocatedVerificationKey::from_witness_and_geometry(&mut cs, &vk_witness, &geometry, &rns_params).unwrap();

//         let one = Num::Variable(AllocatedNum::one(&mut cs));

//         let (valid, scalar) = aggregate_single_for_reference_geometry::<_, GenericTranscriptGadget<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>, _, false>(
//             &mut cs,
//             p,
//             &params,
//             &mut pair_with_gen_accumulator,
//             &mut pair_with_x_accumulator,
//             &vk,
//             &one,
//             &rns_params,
//         ).unwrap();

//         assert!(!valid.get_value().unwrap());
//         assert!(scalar.get_value().unwrap().is_zero());

//         let generator = PointAffine::constant(G1Affine::one(), &rns_params);
//         let generator = mask_point(&mut cs, &valid, generator).unwrap();

//         let pair = (scalar, generator);
//         pair.accumulate_into(&mut cs, &mut pair_with_gen_accumulator).unwrap();

//         println!("Accumulating to pair with generator");
//         dbg!(pair_with_gen_accumulator.multiexp_points.len());
//         let (quasi_result, compensation, base) = pair_with_gen_accumulator.finalize(&mut cs).unwrap();
//         assert_eq!(quasi_result.get_value().unwrap(), base.mul(compensation.get_value().unwrap().into_repr()).into_affine());
//         println!("Accumulating to pair with H^X");
//         dbg!(pair_with_x_accumulator.multiexp_points.len());
//         let (quasi_result, compensation, base) = pair_with_x_accumulator.finalize(&mut cs).unwrap();
//         assert_eq!(quasi_result.get_value().unwrap(), base.mul(compensation.get_value().unwrap().into_repr()).into_affine());

//         println!("Aggregation of one proof with tables taken {} gates", cs.get_current_step_number());

//         println!("Checking if satisfied");
//         assert!(cs.is_satisfied());
//     }

//     #[test]
//     fn test_range_tables_to_aggregate_valid_proof() {
//         let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         let params = bn254_rescue_params();
//         let (mut cs, _, _) = create_test_artifacts();

//         // // w = 16
//         // inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 16).unwrap();
//         // let info = get_range_constraint_info(&cs);
//         // let info = info[0];

//         // let mut rns_params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
//         //     80,
//         //     110,
//         //     4,
//         //     info,
//         //     true
//         // );
//         // // rns_params.set_prefer_double_limb_carry_propagation(false);

//         // ~2_780_000 constraints for double carry propagation is on

//         // // w = 17
//         // inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 17).unwrap();
//         // let info = get_range_constraint_info(&cs);
//         // let info = info[0];

//         // let mut rns_params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
//         //     68,
//         //     110,
//         //     4,
//         //     info,
//         //     true
//         // );

//         // // ~2_630_000 constraints for double carry propagation is on

//         // w = 20
//         inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 20).unwrap();
//         let info = get_range_constraint_info(&cs);
//         let info = info[0];
//         // ~2_300_000 constraints for double carry propagation is on

//         let mut rns_params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
//             100,
//             110,
//             3,
//             info,
//             true
//         );
//         rns_params.set_prefer_double_limb_carry_propagation(false);

//         // // ~2_580_000 constraints for double carry propagation is off

//         let base_placeholder_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[0];

//         let some_random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[1];

//         let compensation_scalar: Fr = rng.gen();

//         let mut pair_with_gen_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let mut pair_with_x_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let (vk, proof) = create_vk_and_proof_for_range_table_params(rns_params.clone());

//         let transcript_params = (&params, &rns_params);
//         let valid = verify::<Bn256, _, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//             &vk,
//             &proof,
//             Some(transcript_params),
//         ).unwrap();

//         assert!(valid);

//         let ((pair_with_gen_value, pair_with_x_value), success) = aggregate::<Bn256, _, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//             &vk,
//             &proof,
//             Some(transcript_params),
//         ).unwrap();

//         assert!(success);

//         let p = ProofInRns {
//             proof: Some(proof),
//             rns_params: &rns_params,
//         };

//         let v = VkInRns {
//             vk: Some(vk),
//             rns_params: &rns_params,
//         };

//         let proof_witness: Vec<_> = p.encode().unwrap().into_iter().map(|el| Some(el)).collect();
//         let vk_witness: Vec<_> = v.encode().unwrap().into_iter().map(|el| Some(el)).collect();

//         let geometry = GeometryHint::hint_for_reference_geometry();

//         // let proof = AllocatedProof::from_witness_and_geometry(&mut cs, &proof_witness, &geometry, &rns_params).unwrap();
//         let vk = AllocatedVerificationKey::from_witness_and_geometry(&mut cs, &vk_witness, &geometry, &rns_params).unwrap();

//         let one = Num::Variable(AllocatedNum::one(&mut cs));

//         let zero_placeholder_point = PointAffine::zero(some_random_point, &rns_params);

//         let (valid, scalar) = aggregate_single_for_reference_geometry::<_, GenericTranscriptGadget<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>, _, false>(
//             &mut cs,
//             p,
//             &params,
//             &mut pair_with_gen_accumulator,
//             &mut pair_with_x_accumulator,
//             &vk,
//             &one,
//             &rns_params,
//         ).unwrap();

//         assert!(valid.get_value().unwrap());

//         let generator = PointAffine::constant(G1Affine::one(), &rns_params);
//         let generator = mask_point(&mut cs, &valid, generator).unwrap();

//         let pair = (scalar, generator);
//         pair.accumulate_into(&mut cs, &mut pair_with_gen_accumulator).unwrap();

//         println!("Accumulating to pair with generator");
//         dbg!(pair_with_gen_accumulator.multiexp_points.len());
//         let partial_with_gen = pair_with_gen_accumulator.finalize_completely(&mut cs).unwrap();
//         assert_eq!(partial_with_gen.get_value().unwrap(), pair_with_gen_value);
//         println!("Accumulating to pair with H^X");
//         dbg!(pair_with_x_accumulator.multiexp_points.len());
//         let partial_with_x = pair_with_x_accumulator.finalize_completely(&mut cs).unwrap();
//         assert_eq!(partial_with_x.get_value().unwrap(), pair_with_x_value);

//         println!("Aggregation of one proof with tables taken {} gates", cs.get_current_step_number());

//         franklin_crypto::plonk::circuit::bigint::single_table_range_constraint::print_stats();
//         println!("Spent {} constraints in equality checks", franklin_crypto::plonk::circuit::counter::output_counter());

//         println!("Checking if satisfied");
//         assert!(cs.is_satisfied());
//     }

//     #[test]
//     fn test_valid_proof_with_challenge() {
//         let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         let params = bn254_rescue_params();
//         let (mut cs, _, _) = create_test_artifacts();

//         // w = 17
//         inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 17).unwrap();
//         let info = get_range_constraint_info(&cs);
//         let info = info[0];

//         let rns_params = RnsParameters::<Bn256, Fq>::new_for_field_with_strategy(
//             68,
//             110,
//             4,
//             info,
//             true
//         );

//         let base_placeholder_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[0];

//         let some_random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256>(
//             b"G1Acc",
//             2
//         )[1];

//         let compensation_scalar: Fr = rng.gen();

//         let mut pair_with_gen_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let mut pair_with_x_accumulator = PartialHomomorphicAccumulator::init(
//             &mut cs,
//             base_placeholder_point,
//             compensation_scalar,
//             &rns_params,
//             Num::Constant(Fr::zero())
//         ).unwrap();

//         let (vk, proof) = create_vk_and_proof_for_range_table_params(rns_params.clone());

//         let transcript_params = (&params, &rns_params);
//         let valid = verify::<Bn256, _, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//             &vk,
//             &proof,
//             Some(transcript_params),
//         ).unwrap();

//         assert!(valid);

//         let ((pair_with_gen_value, pair_with_x_value), success) = aggregate::<Bn256, _, GenericTranscriptForRNSInFieldOnly<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>>(
//             &vk,
//             &proof,
//             Some(transcript_params),
//         ).unwrap();

//         assert!(success);

//         let p = ProofInRns {
//             proof: Some(proof),
//             rns_params: &rns_params,
//         };

//         let v = VkInRns {
//             vk: Some(vk),
//             rns_params: &rns_params,
//         };

//         let proof_witness: Vec<_> = p.encode().unwrap().into_iter().map(|el| Some(el)).collect();
//         let vk_witness: Vec<_> = v.encode().unwrap().into_iter().map(|el| Some(el)).collect();

//         let geometry = GeometryHint::hint_for_reference_geometry();

//         // let proof = AllocatedProof::from_witness_and_geometry(&mut cs, &proof_witness, &geometry, &rns_params).unwrap();
//         let vk = AllocatedVerificationKey::from_witness_and_geometry(&mut cs, &vk_witness, &geometry, &rns_params).unwrap();

//         let fs_challenge_value: Fr = Fr::from_str("2").unwrap();
//         let fs_challenge = Num::Variable(AllocatedNum::alloc(&mut cs, || Ok(fs_challenge_value)).unwrap());

//         let zero_placeholder_point = PointAffine::zero(some_random_point, &rns_params);

//         let (valid, scalar) = aggregate_single_for_reference_geometry::<_, GenericTranscriptGadget<Bn256, RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>, AWIDTH_VALUE, SWIDTH_VALUE>, _, false>(
//             &mut cs,
//             p,
//             &params,
//             &mut pair_with_gen_accumulator,
//             &mut pair_with_x_accumulator,
//             &vk,
//             &fs_challenge,
//             &rns_params,
//         ).unwrap();

//         assert!(valid.get_value().unwrap());

//         let generator = PointAffine::constant(G1Affine::one(), &rns_params);
//         let generator = mask_point(&mut cs, &valid, generator).unwrap();

//         let pair = (scalar, generator);
//         pair.accumulate_into(&mut cs, &mut pair_with_gen_accumulator).unwrap();

//         println!("Accumulating to pair with generator");
//         let partial_with_gen = pair_with_gen_accumulator.finalize_completely(&mut cs).unwrap();
//         assert_eq!(partial_with_gen.get_value().unwrap(), pair_with_gen_value.mul(fs_challenge_value.into_repr()).into_affine());
//         println!("Accumulating to pair with H^X");
//         let partial_with_x = pair_with_x_accumulator.finalize_completely(&mut cs).unwrap();
//         assert_eq!(partial_with_x.get_value().unwrap(), pair_with_x_value.mul(fs_challenge_value.into_repr()).into_affine());

//         println!("Aggregation of one proof with tables taken {} gates", cs.get_current_step_number());

//         println!("Checking if satisfied");
//         assert!(cs.is_satisfied());
//         assert_eq!(cs.sorted_gates.len(), 2);
//     }
// }
