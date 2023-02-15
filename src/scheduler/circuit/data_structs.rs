use super::*;

pub(crate) fn address_to_u256<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: &UInt160<E>,
) -> Result<UInt256<E>, SynthesisError> {
    let chunks =
        split_some_into_fixed_number_of_limbs(value.get_value().map(|el| el.into()), 64, 3);
    let mut result = UInt256::zero();
    use num_traits::ToPrimitive;
    for (i, c) in chunks.into_iter().enumerate() {
        let value = c.map(|el| el.to_u64().unwrap());
        let limb = UInt64::allocate(cs, value)?;
        result.inner[i] = limb;
    }

    let shifts = compute_shifts::<E::Fr>();
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&result.inner[0].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&result.inner[1].inner, shifts[64]);
    lc.add_assign_number_with_coeff(&result.inner[2].inner, shifts[128]);
    lc.add_assign_number_with_coeff(&value.inner, minus_one);
    lc.enforce_zero(cs)?;

    Ok(result)
}

pub(crate) fn u32_to_u256<E: Engine>(value: UInt32<E>) -> Result<UInt256<E>, SynthesisError> {
    let mut result = UInt256::zero();
    result.inner[0] = UInt64::from_num_unchecked(value.inner);

    Ok(result)
}

pub(crate) fn u64_to_u256<E: Engine>(value: UInt64<E>) -> Result<UInt256<E>, SynthesisError> {
    let mut result = UInt256::zero();
    result.inner[0] = value;

    Ok(result)
}

pub(crate) fn u256_to_address_checked<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: UInt256<E>,
) -> Result<(UInt160<E>, Boolean), SynthesisError> {
    let word_2_limbs = value.inner[2].decompose_into_uint16_in_place(cs)?;

    let shifts = compute_shifts::<E::Fr>();

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&value.inner[0].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&value.inner[1].inner, shifts[64]);
    lc.add_assign_number_with_coeff(&word_2_limbs[0].inner, shifts[128]);
    lc.add_assign_number_with_coeff(&word_2_limbs[1].inner, shifts[128 + 16]);
    let num = lc.into_num(cs)?;

    let result = UInt160::from_num_unchecked(num);

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&word_2_limbs[2].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&word_2_limbs[3].inner, shifts[16]);
    lc.add_assign_number_with_coeff(&value.inner[3].inner, shifts[16 + 16]);
    let num = lc.into_num(cs)?;
    let is_valid = num.is_zero(cs)?;

    Ok((result, is_valid))
}

pub(crate) fn u256_to_u32_checked<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: UInt256<E>,
) -> Result<(UInt32<E>, Boolean), SynthesisError> {
    let word_0_limbs = value.inner[0].decompose_into_uint16_in_place(cs)?;

    let shifts = compute_shifts::<E::Fr>();

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&word_0_limbs[0].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&word_0_limbs[1].inner, shifts[16]);
    let num = lc.into_num(cs)?;

    let result = UInt32::from_num_unchecked(num);

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&value.inner[2].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&value.inner[3].inner, shifts[64]);
    let num = lc.into_num(cs)?;
    let t0 = num.is_zero(cs)?;

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&word_0_limbs[2].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&word_0_limbs[3].inner, shifts[16]);
    lc.add_assign_number_with_coeff(&value.inner[1].inner, shifts[16 + 16]);
    let num = lc.into_num(cs)?;
    let t1 = num.is_zero(cs)?;

    let is_valid = smart_and(cs, &[t0, t1])?;

    Ok((result, is_valid))
}

pub(crate) fn u256_to_u64_checked<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: UInt256<E>,
) -> Result<(UInt64<E>, Boolean), SynthesisError> {
    let shifts = compute_shifts::<E::Fr>();

    let result = value.inner[0];

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&value.inner[1].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&value.inner[2].inner, shifts[64]);
    lc.add_assign_number_with_coeff(&value.inner[3].inner, shifts[128]);
    let num = lc.into_num(cs)?;
    let is_valid = num.is_zero(cs)?;

    Ok((result, is_valid))
}

pub(crate) fn u256_to_num_checked<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: UInt256<E>,
) -> Result<(Num<E>, Boolean), SynthesisError> {
    let shifts = compute_shifts::<E::Fr>();

    let mut modulus_minus_one = BigUint::from(0u64);
    for limb in E::Fr::char().as_ref().iter().rev() {
        modulus_minus_one += BigUint::from(*limb);
        modulus_minus_one <<= 64;
    }
    modulus_minus_one -= BigUint::from(1u64);
    let modulus_minus_one = UInt256::constant_from_biguint(modulus_minus_one);

    let (_, uf) = modulus_minus_one.sub(cs, &value)?;

    let is_valid = uf.not();

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&value.inner[0].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&value.inner[1].inner, shifts[64]);
    lc.add_assign_number_with_coeff(&value.inner[2].inner, shifts[128]);
    lc.add_assign_number_with_coeff(&value.inner[3].inner, shifts[192]);
    let result = lc.into_num(cs)?;

    Ok((result, is_valid))
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct ContractFactoryRecord<E: Engine> {
    pub exists: Boolean,
    pub known_in_rollup: Boolean,
    pub _marker: std::marker::PhantomData<E>,
}

impl<E: Engine> ContractFactoryRecord<E> {
    pub fn from_uint256<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        encoding: &UInt256<E>,
    ) -> Result<Self, SynthesisError> {
        // we assume that last BE byte is 0 or 1 indicating presence, one byte before last is
        // indicator of rollup/porter
        let last_8_be_bytes = encoding.inner[0].into_be_bytes(cs)?;
        assert_eq!(last_8_be_bytes.len(), 8);
        let byte_true = Byte::constant(1u8);

        let exists_byte = last_8_be_bytes[7];
        let known_in_rollup_byte = last_8_be_bytes[6];
        let exists = Num::equals(cs, &exists_byte.inner, &byte_true.inner)?;
        let known_in_rollup = Num::equals(cs, &known_in_rollup_byte.inner, &byte_true.inner)?;

        let new = Self {
            exists,
            known_in_rollup,
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    pub fn into_uint256<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<UInt256<E>, SynthesisError> {
        let mut encoding = UInt256::zero();
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&self.exists, shifts[0]);
        lc.add_assign_boolean_with_coeff(&self.known_in_rollup, shifts[8]);
        let num = lc.into_num(cs)?;
        encoding.inner[0] = UInt64::from_num_unchecked(num);

        Ok(encoding)
    }
}

use franklin_crypto::generic_twisted_edwards::TwistedEdwardsCurveParams;

#[derive(Clone, Debug, Copy)]
pub struct MarkerTwistedEdwardsCurveParams;

impl<E: Engine> TwistedEdwardsCurveParams<E> for MarkerTwistedEdwardsCurveParams {
    type Fs = crate::franklin_crypto::alt_babyjubjub::fs::Fs;

    fn is_param_a_equals_minus_one(&self) -> bool {
        unimplemented!();
    }
    fn param_d(&self) -> E::Fr {
        unimplemented!();
    }
    fn param_a(&self) -> E::Fr {
        unimplemented!();
    }
    fn generator(&self) -> TwistedEdwardsPoint<E> {
        unimplemented!();
    }
    fn log_2_cofactor(&self) -> usize {
        unimplemented!();
    }
}
