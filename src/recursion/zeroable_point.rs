use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct PointAffine<'a, E: Engine, G: CurveAffine>
where
    <G as CurveAffine>::Base: PrimeField,
{
    pub(crate) non_zero_point: AffinePoint<'a, E, G>,
    pub(crate) is_zero: Boolean,
}

impl<'a, E: Engine, G: CurveAffine> PointAffine<'a, E, G>
where
    <G as CurveAffine>::Base: PrimeField,
{
    pub fn allocate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<G>,
        placeholder_value: G,
        rns_params: &'a RnsParameters<E, G::Base>,
    ) -> Result<Self, SynthesisError> {
        assert!(!placeholder_value.is_zero());

        let (to_allocate, is_zero) = if let Some(v) = value {
            if v.is_zero() {
                (Some(placeholder_value), Some(true))
            } else {
                (Some(v), Some(false))
            }
        } else {
            (None, None)
        };

        let non_zero_point = AffinePoint::alloc(cs, to_allocate, rns_params)?;
        let b = G::b_coeff();

        let (inner_is_on_curve, non_zero_point) = non_zero_point.is_on_curve_for_zero_a(cs, b)?;

        Boolean::enforce_equal(cs, &inner_is_on_curve, &Boolean::constant(true))?;

        let is_zero = Boolean::from(AllocatedBit::alloc(cs, is_zero)?);

        let new = Self {
            non_zero_point,
            is_zero,
        };

        Ok(new)
    }

    #[track_caller]
    pub fn allocate_non_zero<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<G>,
        _placeholder_value: G,
        rns_params: &'a RnsParameters<E, G::Base>,
    ) -> Result<Self, SynthesisError> {
        assert!(!_placeholder_value.is_zero());
        if let Some(value) = value {
            assert!(!value.is_zero());
        }
        let to_allocate = value;

        let non_zero_point = AffinePoint::alloc(cs, to_allocate, rns_params)?;
        let b = G::b_coeff();

        let (inner_is_on_curve, non_zero_point) = non_zero_point.is_on_curve_for_zero_a(cs, b)?;

        Boolean::enforce_equal(cs, &inner_is_on_curve, &Boolean::constant(true))?;

        let new = Self {
            non_zero_point,
            is_zero: Boolean::constant(false),
        };

        Ok(new)
    }

    pub fn allocate_from_binary_limbs<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        limbs: &[Num<E>],
        rns_params: &'a RnsParameters<E, G::Base>,
    ) -> Result<Self, SynthesisError> {
        let is_zero = is_all_zeroes(cs, limbs)?;

        assert_eq!(
            limbs.len(),
            rns_params.num_limbs_for_in_field_representation * 2
        );

        let (x_limbs, y_limbs) = limbs.split_at(rns_params.num_limbs_for_in_field_representation);

        let mut x_limbs = x_limbs.to_vec();
        x_limbs.resize(rns_params.num_binary_limbs, Num::Constant(E::Fr::zero()));

        let mut y_limbs = y_limbs.to_vec();
        y_limbs.resize(rns_params.num_binary_limbs, Num::Constant(E::Fr::zero()));

        // allocate coordinates
        let x = FieldElement::coarsely_allocate_from_single_limb_witnesses(
            cs, &x_limbs, false, rns_params,
        )?;

        let y = FieldElement::coarsely_allocate_from_single_limb_witnesses(
            cs, &y_limbs, false, rns_params,
        )?;

        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => Some(G::from_xy_unchecked(x, y)),
            _ => None,
        };

        let point = AffinePoint { x, y, value };

        let b = G::b_coeff();

        let (inner_is_on_curve, point) = point.is_on_curve_for_zero_a(cs, b)?;

        // we allow point to be garbage if it's zero, otherwise it must be on curve
        can_not_be_false_if_flagged(cs, &inner_is_on_curve, &is_zero.not())?;

        let zeroable_point = Self {
            non_zero_point: point,
            is_zero: is_zero,
        };

        Ok(zeroable_point)
    }

    pub fn allocate_from_in_field_binary_limbs<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        limbs: &[Num<E>],
        rns_params: &'a RnsParameters<E, G::Base>,
    ) -> Result<Self, SynthesisError> {
        let is_zero = is_all_zeroes(cs, limbs)?;

        assert_eq!(
            limbs.len(),
            rns_params.num_limbs_for_in_field_representation * 2
        );

        let (x_limbs, y_limbs) = limbs.split_at(rns_params.num_limbs_for_in_field_representation);
        // allocate coordinates
        let x =
            FieldElement::allocate_from_single_limb_witnesses_in_field(cs, &x_limbs, rns_params)?;
        let y =
            FieldElement::allocate_from_single_limb_witnesses_in_field(cs, &y_limbs, rns_params)?;

        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_checked(x, y).unwrap())
                // Some(G::from_xy_unchecked(x, y))
            }
            _ => None,
        };

        let point = AffinePoint { x, y, value };

        let b = G::b_coeff();

        let (inner_is_on_curve, point) = point.is_on_curve_for_zero_a(cs, b)?;

        // we allow point to be garbage if it's zero, otherwise it must be on curve
        can_not_be_false_if_flagged(cs, &inner_is_on_curve, &is_zero.not())?;

        let zeroable_point = Self {
            non_zero_point: point,
            is_zero: is_zero,
        };

        Ok(zeroable_point)
    }

    pub fn allocate_from_in_field_binary_limbs_non_zero<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        limbs: &[Num<E>],
        rns_params: &'a RnsParameters<E, G::Base>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            limbs.len(),
            rns_params.num_limbs_for_in_field_representation * 2
        );

        let (x_limbs, y_limbs) = limbs.split_at(rns_params.num_limbs_for_in_field_representation);
        let is_zero = is_all_zeroes(cs, x_limbs)?;
        Boolean::enforce_equal(cs, &is_zero, &Boolean::constant(false))?;
        let is_zero = is_all_zeroes(cs, y_limbs)?;
        Boolean::enforce_equal(cs, &is_zero, &Boolean::constant(false))?;

        // allocate coordinates
        let x =
            FieldElement::allocate_from_single_limb_witnesses_in_field(cs, &x_limbs, rns_params)?;
        let y =
            FieldElement::allocate_from_single_limb_witnesses_in_field(cs, &y_limbs, rns_params)?;

        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_checked(x, y).unwrap())
                // Some(G::from_xy_unchecked(x, y))
            }
            _ => None,
        };

        let point = AffinePoint { x, y, value };

        let b = G::b_coeff();

        let (inner_is_on_curve, point) = point.is_on_curve_for_zero_a(cs, b)?;
        Boolean::enforce_equal(cs, &inner_is_on_curve, &Boolean::constant(true))?;

        let zeroable_point = Self {
            non_zero_point: point,
            is_zero: Boolean::constant(false),
        };

        Ok(zeroable_point)
    }

    pub fn constant(value: G, rns_params: &'a RnsParameters<E, G::Base>) -> Self {
        assert!(!value.is_zero());
        let is_zero = Boolean::constant(value.is_zero());
        let point = AffinePoint::constant(value, rns_params);

        let zeroable_point = Self {
            non_zero_point: point,
            is_zero: is_zero,
        };

        zeroable_point
    }

    pub fn zero(placeholder_value: G, rns_params: &'a RnsParameters<E, G::Base>) -> Self {
        assert!(!placeholder_value.is_zero());
        let is_zero = Boolean::constant(true);
        let point = AffinePoint::constant(placeholder_value, rns_params);

        let zeroable_point = Self {
            non_zero_point: point,
            is_zero: is_zero,
        };

        zeroable_point
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        first: Self,
        second: Self,
    ) -> Result<Self, SynthesisError> {
        if let Boolean::Constant(constant) = flag {
            if *constant {
                return Ok(first);
            } else {
                return Ok(second);
            }
        }
        // select boolean
        let select_first = Boolean::and(cs, &flag, &first.is_zero)?;
        let select_second = Boolean::and(cs, &flag.not(), &second.is_zero)?;
        let is_zero = Boolean::or(cs, &select_first, &select_second)?;
        let (point, _) =
            AffinePoint::select(cs, flag, first.non_zero_point, second.non_zero_point)?;

        let zeroable_point = Self {
            non_zero_point: point,
            is_zero: is_zero,
        };

        Ok(zeroable_point)
    }
}

pub fn is_all_zeroes<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    values: &[Num<E>],
) -> Result<Boolean, SynthesisError> {
    let mut lc = LinearCombination::zero();
    for v in values.iter() {
        let not_zero = v.is_zero(cs)?.not();
        lc.add_assign_boolean_with_coeff(&not_zero, E::Fr::one());
    }

    let as_num = lc.into_num(cs)?;
    let all_are_zero = as_num.is_zero(cs)?;

    Ok(all_are_zero)
}

fn check_consistency<'a, E: Engine, G: CurveAffine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    is_zero: &Boolean,
    allocated_point: &AffinePoint<'a, E, G>,
) -> Result<(), SynthesisError>
where
    <G as CurveAffine>::Base: PrimeField,
{
    let mut lc = LinearCombination::zero();
    let params = &allocated_point.x.representation_params;
    // if any of the elements below are NOT zero then LC will be != 0
    for coord in [&allocated_point.x, &allocated_point.y].iter() {
        assert_eq!(coord.binary_limbs.len(), params.num_binary_limbs);
        for limb in coord.binary_limbs.iter() {
            let as_num = limb.collapse_into_num(cs)?;
            let not_zero = as_num.is_zero(cs)?.not();
            lc.add_assign_boolean_with_coeff(&not_zero, E::Fr::one());
        }
        let as_num = coord.base_field_limb.collapse_into_num(cs)?;
        let not_zero = as_num.is_zero(cs)?.not();
        lc.add_assign_boolean_with_coeff(&not_zero, E::Fr::one());
    }
    let as_num = lc.into_num(cs)?;
    let all_limbs_are_zero = as_num.is_zero(cs)?;

    Boolean::enforce_equal(cs, &all_limbs_are_zero, is_zero)?;

    Ok(())
}

impl<
        'a,
        E: Engine,
        A: Accumulator<
            E,
            NonTrivialElement = (Num<E>, AffinePoint<'a, E, E::G1Affine>),
            TrivialElement = Num<E>,
        >,
    > Accumulable<E, A> for (Num<E>, PointAffine<'a, E, E::G1Affine>)
{
    fn accumulate_into<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        accumulator: &mut A,
    ) -> Result<(), SynthesisError> {
        // we need to make a scalar for compensation
        // and some non-zero pair for accumulation
        let (compensation_scalar, (one, compensation_point)) = accumulator.get_placeholders();

        let zero = Num::Constant(E::Fr::zero());

        let point_is_zero = &self.1.is_zero;
        // if point is zero add compensation_scalar * compensation_point now
        // and add +compensation_scalar to the trivial elements (we do subtraction in the accumulator)
        // else we add scalar * point now and zero into compensation_scalar

        let scalar_into_accumulator = Num::conditionally_select(cs, point_is_zero, &one, &self.0)?;
        let scalar_into_compensation =
            Num::conditionally_select(cs, point_is_zero, &compensation_scalar, &zero)?;

        let (point_to_add, _) = AffinePoint::select(
            cs,
            point_is_zero,
            compensation_point,
            self.1.non_zero_point.clone(),
        )?;

        accumulator.add_trivial(cs, scalar_into_compensation)?;
        accumulator.add_non_trivial(cs, (scalar_into_accumulator, point_to_add))?;

        Ok(())
    }
}
