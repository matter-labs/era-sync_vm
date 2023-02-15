use super::accumulator::*;
use super::partial_accumulator::*;
use super::zeroable_point::*;
use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct KateCommitment<'a, E: Engine, G: CurveAffine<Scalar = E::Fr>>
where
    <G as CurveAffine>::Base: PrimeField,
{
    pub(crate) commitment: PointAffine<'a, E, G>,
    pub(crate) opening_point: Option<AllocatedNum<E>>, // it should be variable for any reasonable means
    pub(crate) opening_value: Option<AllocatedNum<E>>, // it should be variable for any reasonable means
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct MultiOpening<'a, E: Engine, G: CurveAffine<Scalar = E::Fr>>
where
    <G as CurveAffine>::Base: PrimeField,
{
    pub(crate) commitments: Vec<(Num<E>, PointAffine<'a, E, G>)>,
    pub(crate) opening_point: AllocatedNum<E>,
    pub(crate) next_factor: Num<E>,
    pub(crate) accumulated_opening: Num<E>,
    pub(crate) delinearization_factor: Num<E>,
}

impl<'a, E: Engine, G: CurveAffine<Scalar = E::Fr>> MultiOpening<'a, E, G>
where
    <G as CurveAffine>::Base: PrimeField,
{
    #[track_caller]
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        first_commitment: KateCommitment<'a, E, G>,
        delinearization: AllocatedNum<E>,
        optional_next_level_delinearization: Option<AllocatedNum<E>>,
    ) -> Result<Self, SynthesisError> {
        assert!(
            first_commitment.opening_point.is_some(),
            "opening point must be known at this stage"
        );
        assert!(first_commitment.opening_value.is_some());

        let z = first_commitment.opening_point.as_ref().unwrap().clone();

        let mut next_factor = Num::Variable(delinearization);
        let mut opening = Num::Variable(first_commitment.opening_value.as_ref().unwrap().clone());
        let mut first_coeff = Num::Variable(AllocatedNum::one(cs));

        if let Some(delin) = optional_next_level_delinearization {
            let as_num = Num::Variable(delin);
            next_factor = next_factor.mul(cs, &as_num)?;
            opening = opening.mul(cs, &as_num)?;
            first_coeff = as_num;
        }

        let new = Self {
            commitments: vec![(first_coeff, first_commitment.commitment)],
            opening_point: z,
            next_factor: next_factor,
            accumulated_opening: opening,
            delinearization_factor: Num::Variable(delinearization),
        };

        Ok(new)
    }

    #[track_caller]
    pub fn new_at_point<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        at: &AllocatedNum<E>,
        delinearization: AllocatedNum<E>,
        optional_next_level_delinearization: Option<AllocatedNum<E>>,
    ) -> Result<Self, SynthesisError> {
        let z = at.clone();

        let mut next_factor = Num::Constant(E::Fr::one());
        let opening = Num::Constant(E::Fr::zero());

        if let Some(delin) = optional_next_level_delinearization {
            let as_num = Num::Variable(delin);
            next_factor = next_factor.mul(cs, &as_num)?;
        }

        let new = Self {
            commitments: vec![],
            opening_point: z,
            next_factor: next_factor,
            accumulated_opening: opening,
            delinearization_factor: Num::Variable(delinearization),
        };

        Ok(new)
    }

    #[track_caller]
    pub fn add_raw_commitment<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        comm: &PointAffine<'a, E, G>,
        val: Num<E>,
    ) -> Result<(), SynthesisError> {
        let mut factor = self.next_factor.clone();
        self.commitments.push((factor, comm.clone()));

        // check for zero point in commitment
        let point_is_zero = &comm.is_zero;
        let value_is_zero = val.is_zero(cs)?;
        // is point is zero then value must be zero
        can_not_be_false_if_flagged(cs, &value_is_zero, point_is_zero)?;

        // add opening value into the accumulated scalar
        let opening = val.mul(cs, &factor)?;
        self.accumulated_opening = self.accumulated_opening.add(cs, &opening)?;

        // bump factor
        factor = factor.mul(cs, &self.delinearization_factor)?;

        self.next_factor = factor;

        Ok(())
    }

    #[track_caller]
    pub fn add_single_commitment<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        c: &KateCommitment<'a, E, G>,
    ) -> Result<(), SynthesisError> {
        let mut factor = self.next_factor.clone();
        assert!(
            c.opening_point.is_some(),
            "opening point must be known at this stage"
        );
        assert!(c.opening_value.is_some());
        assert!(
            self.opening_point.get_variable() == c.opening_point.as_ref().unwrap().get_variable(),
            "commitments must be opened at the same point"
        );
        self.commitments.push((factor, c.commitment.clone()));

        // check for zero point in commitment
        let point_is_zero = &c.commitment.is_zero;
        let value_is_zero = c.opening_value.as_ref().unwrap().is_zero(cs)?;
        // is point is zero then value must be zero
        can_not_be_false_if_flagged(cs, &value_is_zero, point_is_zero)?;

        // add opening value into the accumulated scalar
        let mut opening = Num::Variable(c.opening_value.as_ref().unwrap().clone());
        opening = opening.mul(cs, &factor)?;
        self.accumulated_opening = self.accumulated_opening.add(cs, &opening)?;

        // bump factor
        factor = factor.mul(cs, &self.delinearization_factor)?;

        self.next_factor = factor;

        Ok(())
    }

    #[track_caller]
    pub fn add_commitments<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        set: &[KateCommitment<'a, E, G>],
    ) -> Result<(), SynthesisError> {
        for c in set.iter() {
            self.add_single_commitment(cs, c)?;
        }

        Ok(())
    }

    #[track_caller]
    pub fn add_single_virtual_commitment<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        virtual_commitment: &[(Num<E>, PointAffine<'a, E, G>)],
        opening_value: Num<E>,
    ) -> Result<(), SynthesisError> {
        let mut factor = self.next_factor.clone();
        for (coeff, point) in virtual_commitment.iter() {
            let c = coeff.mul(cs, &factor)?;
            // let acc_len = self.commitments.len();
            // let peek_over = 3;
            // // check for multiexp later on
            // let slice = if acc_len >= peek_over {
            //     &self.commitments[(acc_len-peek_over)..]
            // } else {
            //     &self.commitments[..]
            // };
            // for (idx, (_, el)) in slice.iter().enumerate() {
            //     match (el.non_zero_point.get_value(), point.non_zero_point.get_value()) {
            //         (Some(existing), Some(to_add)) => {
            //             assert!(existing != to_add, "added an equal point for virtual committment for index {} with acc len {} with value of {}", idx, acc_len, to_add);
            //         },
            //         _ => {}
            //     }
            // }

            self.commitments.push((c, point.clone()));
        }

        // add opening value into the accumulated scalar
        let opening = opening_value.mul(cs, &factor)?;
        self.accumulated_opening = self.accumulated_opening.add(cs, &opening)?;

        // bump factor
        factor = factor.mul(cs, &self.delinearization_factor)?;

        self.next_factor = factor;

        Ok(())
    }
}

impl<'a, E: Engine> MultiOpening<'a, E, E::G1Affine> {
    #[track_caller]
    pub fn add_into_accumulator_and_split_scalars<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        accumulator: &mut HomomorphicAccumulator<'a, E>,
    ) -> Result<(AllocatedNum<E>, AllocatedNum<E>), SynthesisError> {
        // we place all the points into the accumulator and separately output scalar for multiplication
        // with generator and with opening
        // (f(x) - f(z))/(x - z) = q(x)
        // e(q(x), x) = e(f(x) - f(z) + q(x) * z, 1)
        //
        // so we output z for later multiplication with q(x) and also output \sum alpha^i f_{i}(z)
        // that we have accumulated before

        for pair in self.commitments.into_iter() {
            pair.accumulate_into(cs, accumulator)?;
        }

        Ok((self.opening_point, self.accumulated_opening.get_variable()))
    }

    #[track_caller]
    pub fn add_into_partial_accumulator_and_split_scalars<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        accumulator: &mut PartialHomomorphicAccumulator<'a, E>,
    ) -> Result<(AllocatedNum<E>, AllocatedNum<E>), SynthesisError> {
        // we place all the points into the accumulator and separately output scalar for multiplication
        // with generator and with opening
        // (f(x) - f(z))/(x - z) = q(x)
        // e(q(x), x) = e(f(x) - f(z) + q(x) * z, 1)
        // e(f(x) - f(z) + q(x) * z, 1) * e(-q(x), x) = 1
        //
        // so we output z for later multiplication with q(x) and also output \sum alpha^i f_{i}(z)
        // that we have accumulated before

        for pair in self.commitments.into_iter() {
            pair.accumulate_into(cs, accumulator)?;
        }

        Ok((self.opening_point, self.accumulated_opening.get_variable()))
    }
}

// #[cfg(test)]
// mod test {
//     use crate::testing::create_test_artifacts;
//     use super::*;
//     use crate::ff::*;
//     use rand::{XorShiftRng, SeedableRng, Rng};
//     use crate::traits::*;
//     use crate::bellman::plonk::better_better_cs::cs::*;
//     use crate::data_structures::alg_binary_tree::rescue_impl::StaticGenericBinaryTreeHasher;
//     use crate::pairing::bn256::{Bn256, Fr, Fq, G1Affine};
//     use crate::traits::GenericHasher;
//     use super::super::zeroable_point::*;
//     use super::super::{Accumulator, Accumulable};
//     use crate::bellman::worker::*;
//     use crate::bellman::kate_commitment::*;
//     use crate::bellman::plonk::polynomials::*;

//     #[test]
//     fn test_simple_accumulation() {
//         let worker = Worker::new();
//         let size = 32;

//         let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
//         let monomial = Crs::<Bn256, CrsForMonomialForm>::crs_42(size, &worker);
//         let delinearization: Fr = rng.gen();
//         let mut factor = Fr::one();
//         let mut commitments = vec![];
//         let mut polys = vec![];
//         let mut challenges = vec![];
//         let mut aggregated_commitment = G1Affine::zero().into_projective();

//         for _ in 0..3 {
//             let poly_coeffs: Vec<Fr> = (0..size).into_iter().map(|_| rng.gen()).collect();
//             let poly = Polynomial::from_coeffs(poly_coeffs).unwrap();
//             let commitment = commit_using_monomials(&poly, &monomial, &worker).unwrap();

//             polys.push(poly);
//             commitments.push(commitment);
//             challenges.push(factor);

//             aggregated_commitment.add_assign(&commitment.mul(factor.into_repr()));

//             factor.mul_assign(&delinearization);
//         }

//         // add zero point
//         {
//             let poly_coeffs: Vec<Fr> = vec![Fr::zero(); size];
//             let poly = Polynomial::from_coeffs(poly_coeffs).unwrap();

//             polys.push(poly);
//             commitments.push(G1Affine::zero());
//             challenges.push(factor);

//             factor.mul_assign(&delinearization);
//         }

//         let z: Fr = rng.gen();
//         let mut values = vec![];
//         let mut aggregated_value = Fr::zero();
//         for (p, c) in polys.iter().zip(challenges.iter()) {
//             let value = p.evaluate_at(&worker, z);
//             values.push(value);

//             let mut tmp = value;
//             tmp.mul_assign(&c);
//             aggregated_value.add_assign(&tmp);
//         }

//         let quotient = calculate_batch_opening_quotient_from_monomials::<Bn256>(
//             &polys,
//             &challenges,
//             z,
//             &worker
//         ).unwrap();

//         let opening = commit_using_monomials(&quotient, &monomial, &worker).unwrap();

//         let valid = is_valid_multiopening::<Bn256>(
//             &commitments,
//             z,
//             &values,
//             opening,
//             delinearization,
//             monomial.g2_monomial_bases[1]
//         );

//         assert!(valid);

//         // // invalid case
//         // *values.last_mut().unwrap() = Fr::one();

//         let (mut cs, _, _) = create_test_artifacts();

//         let base_placeholder_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256::G1Affine>(
//             b"G1Acc",
//             2
//         )[0];

//         let some_random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log::<Bn256::G1Affine>(
//             b"G1Acc",
//             2
//         )[1];

//         let compensation_scalar: Fr = rng.gen();

//         let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

//         let mut accumulator = HomomorphicAccumulator::init(&mut cs, base_placeholder_point, compensation_scalar, &params).unwrap();

//         let allocated_delin = AllocatedNum::alloc(&mut cs, || Ok(delinearization)).unwrap();
//         let z_allocated = AllocatedNum::alloc(&mut cs, || Ok(z)).unwrap();
//         let mut multiopening = None;
//         for (c, v) in commitments.iter().zip(values.iter()) {
//             let point = PointAffine::allocate(&mut cs, Some(*c), some_random_point, &params).unwrap();
//             let value = AllocatedNum::alloc(&mut cs, || Ok(*v)).unwrap();
//             let commitment = KateCommitment {
//                 commitment: point,
//                 opening_point: Some(z_allocated),
//                 opening_value: Some(value)
//             };

//             if multiopening.is_none() {
//                 multiopening = Some(MultiOpening::new(
//                     &mut cs,
//                     commitment,
//                     allocated_delin,
//                     None
//                 ).unwrap()
//                 );
//             } else {
//                 let multiopening = multiopening.as_mut().unwrap();
//                 multiopening.add_commitments(&mut cs, &[commitment]).unwrap();
//             }
//         }

//         let multiopening = multiopening.unwrap();

//         let (z_from_multiopening, aggregated_value_allocated) = multiopening.add_into_accumulator_and_split_scalars(
//             &mut cs,
//             &mut accumulator,
//         ).unwrap();

//         let tmp = accumulator.clone();
//         let candidate = tmp.finalize(&mut cs).unwrap();

//         assert_eq!(candidate.get_value().unwrap(), aggregated_commitment.into_affine());
//         assert_eq!(aggregated_value_allocated.get_value().unwrap(), aggregated_value);
//         assert!(z_from_multiopening.get_variable() == z_allocated.get_variable());

//         assert!(cs.is_satisfied());

//         println!("Aggregation of 4 commitments has taken {} gates", cs.get_current_step_number());
//     }

// }
