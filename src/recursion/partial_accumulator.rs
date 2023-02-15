use super::zeroable_point::*;
use super::*;

// partial accumulator does not collapse the compensation scalar into the main
// multiexp result, so we can immediatelly initialize another one and continue the accumulation
#[derive(Clone, Debug)]
pub struct PartialHomomorphicAccumulator<'a, E: Engine> {
    pub(crate) base_placeholder_point: E::G1Affine,
    pub(crate) base_placeholder_scalar_factor: E::Fr,
    pub(crate) current_compensation_scalar: E::Fr,
    pub(crate) multiexp_scalars: Vec<Num<E>>,
    pub(crate) multiexp_points: Vec<AffinePoint<'a, E, E::G1Affine>>,
    pub(crate) allocated_placeholder_point: AffinePoint<'a, E, E::G1Affine>,
    pub(crate) compensation_scalar: Num<E>,
    pub(crate) rns_params: &'a RnsParameters<E, E::Fq>,
}

impl<'a, E: Engine> PartialHomomorphicAccumulator<'a, E> {
    pub fn init<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        placeholder_point: E::G1Affine,
        scalar_factor: E::Fr,
        rns_parameters: &'a RnsParameters<E, E::Fq>,
        initial_compensation_scalar: Num<E>,
    ) -> Result<Self, SynthesisError> {
        assert!(
            !placeholder_point.is_zero(),
            "placeholder point must be random with unknown discrete log and non-zero"
        );
        let allocated_placeholder_point = AffinePoint::constant(placeholder_point, rns_parameters);

        // for now multiexp only deals with variable scalars, so we enforce equal to constant
        let one = Num::Variable(AllocatedNum::alloc(cs, || Ok(E::Fr::one()))?);
        one.get_variable()
            .assert_equal_to_constant(cs, E::Fr::one())?;

        // we add a pair (1 * allocated_placeholder_point) to the accumulator, so we
        // do not need to do 0 * allocated_placeholder_point at the end of the day

        // so don't forget to get +1 into compensation
        let compensation_scalar = initial_compensation_scalar.add(cs, &one)?;

        let new = Self {
            base_placeholder_point: placeholder_point,
            base_placeholder_scalar_factor: scalar_factor,
            current_compensation_scalar: scalar_factor,
            multiexp_scalars: vec![one],
            multiexp_points: vec![allocated_placeholder_point.clone()],
            allocated_placeholder_point,
            compensation_scalar: compensation_scalar,
            rns_params: rns_parameters,
        };

        Ok(new)
    }

    pub fn finalize_completely<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<AffinePoint<'a, E, E::G1Affine>, SynthesisError> {
        assert_eq!(self.multiexp_points.len(), self.multiexp_scalars.len());
        let multiexp_candidate =
            AffinePoint::multiexp(cs, &self.multiexp_scalars, &self.multiexp_points, None)?;

        let (compensation, _) =
            self.allocated_placeholder_point
                .mul(cs, &self.compensation_scalar, None)?;

        let (result, _) = multiexp_candidate.sub_unequal(cs, compensation)?;

        Ok(result)
    }

    pub fn finalize_completely_using_endomorphism<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        endo_params: &EndomorphismParameters<E>,
    ) -> Result<AffinePoint<'a, E, E::G1Affine>, SynthesisError> {
        assert_eq!(self.multiexp_points.len(), self.multiexp_scalars.len());
        let multiexp_candidate = AffinePoint::multiexp_using_endomorphism(
            cs,
            &self.multiexp_scalars,
            &self.multiexp_points,
            endo_params,
        )?;

        let (compensation, _) =
            self.allocated_placeholder_point
                .mul(cs, &self.compensation_scalar, None)?;

        let (result, _) = multiexp_candidate.sub_unequal(cs, compensation)?;

        Ok(result)
    }
}

impl<'a, E: Engine> Accumulator<E> for PartialHomomorphicAccumulator<'a, E> {
    type NonTrivialElement = (Num<E>, AffinePoint<'a, E, E::G1Affine>);
    type TrivialElement = Num<E>;
    type Result = (AffinePoint<'a, E, E::G1Affine>, Num<E>, E::G1Affine);

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

        Ok((
            multiexp_candidate,
            self.compensation_scalar,
            self.base_placeholder_point,
        ))
    }
}

#[track_caller]
pub fn mask_point<'a, E: Engine, CS: ConstraintSystem<E>, G: CurveAffine>(
    cs: &mut CS,
    valid: &Boolean,
    point: PointAffine<'a, E, G>,
) -> Result<PointAffine<'a, E, G>, SynthesisError>
where
    <G as CurveAffine>::Base: PrimeField,
{
    // if valid we do nothing,
    // if valid == false we set point's zeroness flag to "true"
    // valid  || is_zero  ||   set
    //   1          0           0
    //   1          1           1
    //   0          0           1
    //   0          1           1

    // make it is_zero OR NOT(valid)
    let set_zero = Boolean::or(cs, &valid.not(), &point.is_zero)?;
    let mut point = point;
    point.is_zero = set_zero;

    Ok(point)
}

#[track_caller]
pub fn mask_commitment<'a, E: Engine, CS: ConstraintSystem<E>, G: CurveAffine>(
    cs: &mut CS,
    valid: &Boolean,
    comm: (Num<E>, PointAffine<'a, E, G>),
) -> Result<(Num<E>, PointAffine<'a, E, G>), SynthesisError>
where
    <G as CurveAffine>::Base: PrimeField,
{
    let (value, mut point) = comm;
    let set_zero = Boolean::or(cs, &valid.not(), &point.is_zero)?;
    point.is_zero = set_zero;

    let value = Num::conditionally_select(cs, &set_zero, &Num::Constant(E::Fr::zero()), &value)?;

    Ok((value, point))
}

pub fn mask_virtual_commitment_with_value<'a, E: Engine, CS: ConstraintSystem<E>, G: CurveAffine>(
    cs: &mut CS,
    valid: &Boolean,
    value: Num<E>,
    points: Vec<(Num<E>, PointAffine<'a, E, G>)>,
) -> Result<(Num<E>, Vec<(Num<E>, PointAffine<'a, E, G>)>), SynthesisError>
where
    <G as CurveAffine>::Base: PrimeField,
{
    // let mut set_all_zero = Boolean::Constant(true);
    let mut set_zero_lc = LinearCombination::zero();
    let num_terms = points.len();
    for (_, p) in points.iter() {
        // we determine whether we set a specific point to 0
        let set_zero = Boolean::or(cs, &valid.not(), &p.is_zero)?;
        set_zero_lc.add_assign_boolean_with_coeff(&set_zero, E::Fr::one());
        // // check that all should be set to 0
        // set_all_zero = Boolean::and(cs, &set_zero, &set_all_zero)?;
    }
    set_zero_lc.sub_assign_constant(E::Fr::from_str(&num_terms.to_string()).unwrap());
    let set_all_zero = set_zero_lc.into_num(cs)?.is_zero(cs)?;
    let mut points = points;
    for (_, p) in points.iter_mut() {
        let zero = Boolean::or(cs, &set_all_zero, &p.is_zero)?;
        p.is_zero = zero;
    }
    let value =
        Num::conditionally_select(cs, &set_all_zero, &Num::Constant(E::Fr::zero()), &value)?;

    Ok((value, points))
}

pub fn mask_scalar<'a, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    valid: &Boolean,
    value: Num<E>,
) -> Result<Num<E>, SynthesisError> {
    let value = Num::conditionally_select(cs, &valid, &value, &Num::Constant(E::Fr::zero()))?;

    Ok(value)
}
