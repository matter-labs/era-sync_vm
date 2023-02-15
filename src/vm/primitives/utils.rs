use super::*;

pub fn num_into_uint128_pair<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
) -> Result<(UInt128<E>, UInt128<E>), SynthesisError> {
    match num {
        Num::Constant(constant) => {
            let repr = constant.into_repr();

            let low = (repr.as_ref()[0] as u128) + ((repr.as_ref()[1] as u128) << 64);
            let high = (repr.as_ref()[2] as u128) + ((repr.as_ref()[3] as u128) << 64);

            let low = u128_to_fe(low);
            let high = u128_to_fe(high);

            let low = UInt128::constant(low);
            let high = UInt128::constant(high);

            return Ok((high, low));
        }
        Num::Variable(..) => {
            let (witness_high, witness_low) = if let Some(value) = num.get_value() {
                let repr = value.into_repr();

                let low = (repr.as_ref()[0] as u128) + ((repr.as_ref()[1] as u128) << 64);
                let high = (repr.as_ref()[2] as u128) + ((repr.as_ref()[3] as u128) << 64);

                (Some(high), Some(low))
            } else {
                (None, None)
            };

            let high = UInt128::allocate(cs, witness_high)?;
            let low = UInt128::allocate(cs, witness_low)?;

            return Ok((high, low));
        }
    }
}

pub fn num_into_canonical_uint128_pair<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
) -> Result<(UInt128<E>, UInt128<E>), SynthesisError> {
    if num.is_constant() {
        return num_into_uint128_pair(cs, num);
    }

    let (high, low) = num_into_uint128_pair(cs, num)?;

    let (modulus_high, modulus_low) = {
        let mut repr = E::Fr::char();
        let one_repr = E::Fr::one().into_repr();
        repr.sub_noborrow(&one_repr);

        let low = (repr.as_ref()[0] as u128) + ((repr.as_ref()[1] as u128) << 64);
        let high = (repr.as_ref()[2] as u128) + ((repr.as_ref()[3] as u128) << 64);
        let low = u128_to_fe(low);
        let high = u128_to_fe(high);
        let low = UInt128::constant(low);
        let high = UInt128::constant(high);

        (high, low)
    };

    // (modulus-1) - value >= 0

    let (result_witness, borrow) = match (low.get_value(), modulus_low.get_value()) {
        (Some(low), Some(modulus_low)) => {
            let (result, borrow) = modulus_low.overflowing_sub(low);

            (Some(result), Some(borrow))
        }
        _ => (None, None),
    };

    let mut shift = E::Fr::one();
    for _ in 0..128 {
        shift.double();
    }

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let result = UInt128::allocate(cs, result_witness)?;
    let intermediate_borrow = Boolean::from(AllocatedBit::alloc(cs, borrow)?);

    // a - b + borrow = result

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&modulus_low.inner, E::Fr::one());
    lc.add_assign_number_with_coeff(&low.inner, minus_one);
    lc.add_assign_boolean_with_coeff(&intermediate_borrow, shift);
    lc.add_assign_number_with_coeff(&result.inner, minus_one);

    lc.enforce_zero(cs)?;

    constraint_bit_length(cs, &result.inner, 128)?;

    let result_witness = match (
        high.get_value(),
        modulus_high.get_value(),
        intermediate_borrow.get_value(),
    ) {
        (Some(high), Some(modulus_high), Some(borrow)) => {
            // we use canonical representation, so we never borrow
            let (result, borrow) = modulus_high.overflowing_sub(borrow as u128);
            assert!(!borrow);
            let (result, borrow) = result.overflowing_sub(high);
            assert!(!borrow);

            Some(result)
        }
        _ => None,
    };

    let result = UInt128::allocate(cs, result_witness)?;

    // a - b - intermediate_borrow = result

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&modulus_high.inner, E::Fr::one());
    lc.add_assign_number_with_coeff(&high.inner, minus_one);
    lc.add_assign_boolean_with_coeff(&intermediate_borrow, minus_one);
    lc.add_assign_number_with_coeff(&result.inner, minus_one);

    lc.enforce_zero(cs)?;

    constraint_bit_length(cs, &result.inner, 128)?;

    Ok((high, low))
}

/// Caller must ensure that mask is indeed a mask!
#[track_caller]
pub fn multiselection_using_linear_combination<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    mask: &[Boolean],
    values: &[Num<E>],
) -> Result<Num<E>, SynthesisError> {
    assert_eq!(mask.len(), values.len());
    let accumulator = if mask.len() > 0 {
        let mut accumulator = Num::mask(cs, &values[0], &mask[0])?;
        for (value, boolean) in values[1..].iter().zip(mask[1..].iter()) {
            accumulator = value.mask_by_boolean_into_accumulator(cs, boolean, &accumulator)?;
        }
        accumulator
    } else {
        Num::zero()
    };

    Ok(accumulator)
}

/// Caller must ensure that mask is indeed a mask!
#[track_caller]
pub fn bit_multiselection_using_linear_combination<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    mask: &[Boolean],
    values: &[Boolean],
) -> Result<Boolean, SynthesisError> {
    assert_eq!(mask.len(), values.len());
    assert!(mask.len() > 0);
    let mut accumulator = LinearCombination::zero();
    accumulator.add_assign_constant(E::Fr::one());
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    for (value, boolean) in values.iter().zip(mask.iter()) {
        let masked = Boolean::and(cs, &value, &boolean)?;
        accumulator.add_assign_boolean_with_coeff(&masked, minus_one);
    }
    let as_num = accumulator.into_num(cs)?;
    let is_zero = as_num.is_zero(cs)?;
    // if LC is zero then we have selected `true` with mask `true` somewhere,
    // and since we know that mask is indeed a mask we could do it at most once,
    // so if LC is zero then selection result == true

    Ok(is_zero)
}

pub fn compare_uint_128_representations<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &[UInt128<E>],
    b: &[UInt128<E>],
) -> Result<(Boolean, Boolean), SynthesisError> {
    // perform chained long subtraction
    assert_eq!(a.len(), b.len());
    let mut is_zero_bools = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let eq = Num::equals(cs, &a.inner, &b.inner)?;
        is_zero_bools.push(eq);
    }
    let eq = smart_and(cs, &is_zero_bools)?;

    let mut borrow = Boolean::constant(false);
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut shift_128 = E::Fr::one();
    for _ in 0..128 {
        shift_128.double();
    }

    for (a, b) in a.iter().zip(b.iter()) {
        let mut lc = LinearCombination::zero();

        let (c, next_borrow_witness) = match (a.get_value(), b.get_value(), borrow.get_value()) {
            (Some(a), Some(b), Some(previous_borrow)) => {
                let (c, borrow_0) = a.overflowing_sub(b);
                let (c, borrow_1) = c.overflowing_sub(previous_borrow as u128);

                (Some(c), Some(borrow_0 | borrow_1))
            }
            _ => (None, None),
        };
        let c = UInt128::allocate(cs, c)?;
        let next_borrow = Boolean::from(AllocatedBit::alloc(cs, next_borrow_witness)?);
        lc.add_assign_number_with_coeff(&a.inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&b.inner, minus_one);
        lc.add_assign_number_with_coeff(&c.inner, minus_one);
        lc.add_assign_boolean_with_coeff(&next_borrow, shift_128);
        lc.add_assign_boolean_with_coeff(&borrow, minus_one);
        lc.enforce_zero(cs)?;

        borrow = next_borrow;
    }

    // if borrow is true then a < b

    Ok((borrow, eq))
}

pub fn compare_uint_16_representations<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &[UInt16<E>],
    b: &[UInt16<E>],
) -> Result<(Boolean, Boolean), SynthesisError> {
    // perform chained long subtraction
    assert_eq!(a.len(), b.len());
    let mut is_zero_bools = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let eq = Num::equals(cs, &a.inner, &b.inner)?;
        is_zero_bools.push(eq);
    }
    let eq = smart_and(cs, &is_zero_bools)?;

    let mut borrow = Boolean::constant(false);
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut shift_16 = E::Fr::one();
    for _ in 0..16 {
        shift_16.double();
    }

    for (a, b) in a.iter().zip(b.iter()) {
        let mut lc = LinearCombination::zero();

        let (c, next_borrow_witness) = match (a.get_value(), b.get_value(), borrow.get_value()) {
            (Some(a), Some(b), Some(previous_borrow)) => {
                let (c, borrow_0) = a.overflowing_sub(b);
                let (c, borrow_1) = c.overflowing_sub(previous_borrow as u16);

                (Some(c), Some(borrow_0 | borrow_1))
            }
            _ => (None, None),
        };
        let c = UInt16::allocate(cs, c)?;
        let next_borrow = Boolean::from(AllocatedBit::alloc(cs, next_borrow_witness)?);
        lc.add_assign_number_with_coeff(&a.inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&b.inner, minus_one);
        lc.add_assign_number_with_coeff(&c.inner, minus_one);
        lc.add_assign_boolean_with_coeff(&next_borrow, shift_16);
        lc.add_assign_boolean_with_coeff(&borrow, minus_one);
        lc.enforce_zero(cs)?;

        borrow = next_borrow;
    }

    // if borrow is true then a < b

    Ok((borrow, eq))
}

pub fn compare_small_fixed_integer_representations<
    E: Engine,
    CS: ConstraintSystem<E>,
    W: WidthMarker,
>(
    cs: &mut CS,
    a: &[SmallFixedWidthInteger<E, W>],
    b: &[SmallFixedWidthInteger<E, W>],
) -> Result<(Boolean, Boolean), SynthesisError> {
    // perform chained long subtraction
    assert_eq!(a.len(), b.len());
    assert!(W::WIDTH < 128);
    let mut is_zero_bools = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let eq = Num::equals(cs, &a.value, &b.value)?;
        is_zero_bools.push(eq);
    }
    let eq = smart_and(cs, &is_zero_bools)?;

    let mut borrow = Boolean::constant(false);
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut shift = E::Fr::one();
    for _ in 0..W::WIDTH {
        shift.double();
    }

    for (a, b) in a.iter().zip(b.iter()) {
        let mut lc = LinearCombination::zero();

        let (c, next_borrow_witness) = match (
            a.get_value_clamped(),
            b.get_value_clamped(),
            borrow.get_value(),
        ) {
            (Some(a), Some(b), Some(previous_borrow)) => {
                let extra = 1u128 << (W::WIDTH as u32);
                let low_mask = extra - 1;
                let tmp = extra + a - b - (previous_borrow as u128);
                let new_borrow = (tmp >> W::WIDTH as u32) == 0;
                let c = tmp & low_mask;

                (Some(c), Some(new_borrow))
            }
            _ => (None, None),
        };
        let c = SmallFixedWidthInteger::<E, W>::from_u128_witness(cs, c)?;
        let next_borrow = Boolean::from(AllocatedBit::alloc(cs, next_borrow_witness)?);
        lc.add_assign_number_with_coeff(&a.value, E::Fr::one());
        lc.add_assign_number_with_coeff(&b.value, minus_one);
        lc.add_assign_number_with_coeff(&c.value, minus_one);
        lc.add_assign_boolean_with_coeff(&next_borrow, shift);
        lc.add_assign_boolean_with_coeff(&borrow, minus_one);
        lc.enforce_zero(cs)?;

        borrow = next_borrow;
    }

    // if borrow is true then a < b

    Ok((borrow, eq))
}

#[track_caller]
pub fn multiselect_nums<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    flag: &Boolean,
    a: &[Num<E>],
    b: &[Num<E>],
) -> Result<Vec<Num<E>>, SynthesisError> {
    assert_eq!(a.len(), b.len());
    assert!(a.len() > 0);
    let mut results = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let r = Num::conditionally_select(cs, flag, a, b)?;
        results.push(r);
    }

    Ok(results)
}

#[track_caller]
pub fn multiselect_nums_fixed<E: Engine, CS: ConstraintSystem<E>, const N: usize>(
    cs: &mut CS,
    flag: &Boolean,
    a: &[Num<E>; N],
    b: &[Num<E>; N],
) -> Result<[Num<E>; N], SynthesisError> {
    let mut results = [Num::Constant(E::Fr::zero()); N];
    for ((a, b), r) in a.iter().zip(b.iter()).zip(results.iter_mut()) {
        *r = Num::conditionally_select(cs, flag, a, b)?;
    }

    Ok(results)
}

#[track_caller]
pub fn multiselect_booleans_with_multipack<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    flag: &Boolean,
    a: &[Boolean],
    b: &[Boolean],
) -> Result<Vec<Boolean>, SynthesisError> {
    assert_eq!(a.len(), b.len());
    assert!(a.len() > 0);
    let mut results = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let new_witness = match (a.get_value(), b.get_value(), flag.get_value()) {
            (Some(a), Some(b), Some(f)) => {
                if f {
                    Some(a)
                } else {
                    Some(b)
                }
            }
            _ => None,
        };

        let selected_bit = Boolean::alloc(cs, new_witness)?;
        results.push(selected_bit);
    }

    let a_packed = LinearCombination::uniquely_pack_booleans_into_nums(cs, &a)?;
    let b_packed = LinearCombination::uniquely_pack_booleans_into_nums(cs, &b)?;
    let result_packed = LinearCombination::uniquely_pack_booleans_into_nums(cs, &results)?;

    let selected = multiselect_nums(cs, flag, &a_packed, &b_packed)?;
    assert_eq!(selected.len(), result_packed.len());

    for (s, r) in selected.into_iter().zip(result_packed.into_iter()) {
        s.enforce_equal(cs, &r)?;
    }

    Ok(results)
}

pub trait IntoBytesStrict<E: Engine>: Send + Sync {
    fn into_le_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError>;
    fn into_be_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError>;
}

impl<E: Engine> IntoBytesStrict<E> for Num<E> {
    fn into_le_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut num_bytes = (E::Fr::NUM_BITS / 8) as usize;
        if E::Fr::NUM_BITS % 8 != 0 {
            num_bytes += 1;
        }

        assert_eq!(num_bytes, 32);

        let result = match self {
            s @ Num::Variable(_) => {
                use crate::vm::primitives::utils::*;
                // use canonical encoding
                let (high, low) = num_into_canonical_uint128_pair(cs, s)?;
                let mut result = vec![];
                let encoding = low.into_le_bytes(cs)?;
                result.extend(encoding);
                let encoding = high.into_le_bytes(cs)?;
                result.extend(encoding);

                result
            }
            Num::Constant(constant) => {
                let mut result = Vec::with_capacity(num_bytes);
                let witness = split_into_slices(constant, 8, num_bytes);
                for w in witness.into_iter() {
                    let num = Num::Constant(w);
                    let byte = Byte::from_num(cs, num)?;
                    result.push(byte);
                }

                result
            }
        };

        Ok(result)
    }

    fn into_be_bytes_strict<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes_strict(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}
