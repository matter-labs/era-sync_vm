use super::*;

#[derive(Clone, Debug)]
pub struct HomomorphicAccumulator<'a, E: Engine> {
    base_placeholder_point: E::G1Affine,
    base_placeholder_scalar_factor: E::Fr,
    current_compensation_scalar: E::Fr,
    multiexp_scalars: Vec<Num<E>>,
    multiexp_points: Vec<AffinePoint<'a, E, E::G1Affine>>,
    // generator: E::G1Affine,
    // allocated_generator: AffinePoint<'a, E, E::G1Affine>,
    allocated_placeholder_point: AffinePoint<'a, E, E::G1Affine>,
    compensation_scalar: Num<E>,
    rns_params: &'a RnsParameters<E, E::Fq>,
}

impl<'a, E: Engine> HomomorphicAccumulator<'a, E> {
    pub fn init<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        placeholder_point: E::G1Affine,
        scalar_factor: E::Fr,
        rns_parameters: &'a RnsParameters<E, E::Fq>,
    ) -> Result<Self, SynthesisError> {
        // let generator = E::G1Affine::one();
        // let allocated_generator = AffinePoint::constant(generator, rns_parameters);

        let allocated_placeholder_point = AffinePoint::constant(placeholder_point, rns_parameters);

        // for now multiexp only deals with variable scalars, so we enforce equal to constant
        let base_scalar = Num::Variable(AllocatedNum::alloc(cs, || Ok(E::Fr::one()))?);
        base_scalar
            .get_variable()
            .assert_equal_to_constant(cs, E::Fr::one())?;

        // we add a pair (1 * allocated_placeholder_point) to the accumulator, so we
        // do not need to do 0 * allocated_placeholder_point at the end of the day

        let new = Self {
            base_placeholder_point: placeholder_point,
            base_placeholder_scalar_factor: scalar_factor,
            current_compensation_scalar: scalar_factor,
            multiexp_scalars: vec![base_scalar],
            multiexp_points: vec![allocated_placeholder_point.clone()],
            allocated_placeholder_point,
            compensation_scalar: Num::Constant(E::Fr::one()),
            rns_params: rns_parameters,
        };

        Ok(new)
    }
}

impl<'a, E: Engine> Accumulator<E> for HomomorphicAccumulator<'a, E> {
    type NonTrivialElement = (Num<E>, AffinePoint<'a, E, E::G1Affine>);
    type TrivialElement = Num<E>;
    type Result = AffinePoint<'a, E, E::G1Affine>;

    fn get_placeholders(&mut self) -> (Self::TrivialElement, Self::NonTrivialElement) {
        let scalar = self.current_compensation_scalar;
        // add power
        self.current_compensation_scalar
            .mul_assign(&self.base_placeholder_scalar_factor);

        let point = self
            .base_placeholder_point
            .mul(scalar.into_repr())
            .into_affine();

        let scalar = Num::Constant(scalar);
        let point = AffinePoint::constant(point, self.rns_params);

        (scalar, (Num::Constant(E::Fr::one()), point))
    }

    #[track_caller]
    fn add_non_trivial<CS: ConstraintSystem<E>>(
        &mut self,
        _cs: &mut CS,
        element: Self::NonTrivialElement,
    ) -> Result<(), SynthesisError> {
        let (scalar, point) = element;
        // let acc_len = self.multiexp_points.len();
        // let peek_over = 3;
        // let slice = if acc_len >= peek_over {
        //     &self.multiexp_points[(acc_len - peek_over)..]
        // } else {
        //     &self.multiexp_points[..]
        // };

        // for (idx, el) in slice.iter().enumerate() {
        //     match (el.get_value(), point.get_value()) {
        //         (Some(existing), Some(to_add)) => {
        //             assert!(existing != to_add, "added an equal point for multiexp for index {} with acc len {} with value of {}", idx, acc_len, to_add);
        //         },
        //         _ => {}
        //     }
        // }
        self.multiexp_scalars.push(scalar);
        self.multiexp_points.push(point);

        Ok(())
    }
    fn add_trivial<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        element: Self::TrivialElement,
    ) -> Result<(), SynthesisError> {
        let new_scalar = self.compensation_scalar.add(cs, &element)?;
        self.compensation_scalar = new_scalar;

        Ok(())
    }
    fn finalize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<Self::Result, SynthesisError> {
        assert_eq!(self.multiexp_points.len(), self.multiexp_scalars.len());
        let multiexp_candidate =
            AffinePoint::multiexp(cs, &self.multiexp_scalars, &self.multiexp_points, None)?;

        let (compensation, _) =
            self.allocated_placeholder_point
                .mul(cs, &self.compensation_scalar, None)?;

        let (result, _) = multiexp_candidate.sub_unequal(cs, compensation)?;

        Ok(result)
    }
}

// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::ff::*;
//     use rand::{XorShiftRng, SeedableRng, Rng};
//     use crate::testing::*;
//     use crate::traits::*;
//     use crate::bellman::plonk::better_better_cs::cs::*;
//     use crate::data_structures::alg_binary_tree::rescue_impl::StaticGenericBinaryTreeHasher;
//     use crate::pairing::bn256::{Bn256, Fr, Fq, G1Affine};
//     use crate::traits::GenericHasher;
//     use super::super::zeroable_point::*;
//     use super::super::{Accumulator, Accumulable};

//     #[test]
//     fn test_accumulator() {
//         const NUM_POINTS: usize = 10;
//         let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

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

//         let mut result = G1Affine::zero().into_projective();
//         for _ in 0..NUM_POINTS {
//             let is_zero: bool = rng.gen();
//             let point = if is_zero {
//                 G1Affine::zero()
//             } else {
//                 let point: G1Affine = rng.gen();
//                 point
//             };

//             let scalar: Fr = rng.gen();
//             result.add_assign(&point.mul(scalar.into_repr()));

//             let allocated_point = PointAffine::allocate(
//                 &mut cs,
//                 Some(point),
//                 some_random_point,
//                 &params
//             ).unwrap();

//             assert!(allocated_point.is_zero.get_value().unwrap() == is_zero);

//             let allocated_scalar = Num::Variable(
//                 AllocatedNum::alloc(&mut cs, || Ok(scalar)).unwrap()
//             );

//             let pair = (allocated_scalar, allocated_point);

//             pair.accumulate_into(&mut cs, &mut accumulator).unwrap();
//         }

//         // let mut a = compensation_scalar;
//         // for _ in 0..NUM_POINTS {
//         //     dbg!(a);
//         //     dbg!(base_placeholder_point.mul(a.into_repr()).into_affine());
//         //     a.mul_assign(&compensation_scalar);
//         // }

//         // for (s, p) in accumulator.multiexp_scalars.iter().zip(accumulator.multiexp_points.iter()) {
//         //     dbg!(s.get_value());
//         //     dbg!(p.get_value());
//         // }

//         // dbg!(&accumulator.compensation_scalar);

//         let accumulation_result = accumulator.finalize(&mut cs).unwrap();
//         let value = accumulation_result.get_value().unwrap();

//         assert_eq!(value, result.into_affine());
//         println!("Multiexp of {} potentially zero points taken {} gates", NUM_POINTS, cs.get_current_step_number());
//         assert!(cs.is_satisfied());
//     }
// }
