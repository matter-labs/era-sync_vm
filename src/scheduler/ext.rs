use super::*;

impl<E: Engine> UInt256<E> {
    pub fn add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(Self, Boolean), SynthesisError> {
        let (result, overflow) = UInt256::make_witness_for_addition(self, other);
        let result = Self::alloc_from_biguint(cs, result)?;
        let overflow = Boolean::alloc(cs, overflow)?;

        let intermediate_of_witness = match (self.get_value(), other.get_value()) {
            (Some(a), Some(b)) => {
                let modulus = BigUint::from(1u64) << 128u32;
                let of = ((a % &modulus) + (b % &modulus)) >> 128u8;

                use num_traits::Zero;
                Some(!of.is_zero())
            }
            _ => None,
        };

        let intermediate_of = Boolean::alloc(cs, intermediate_of_witness)?;

        // enforce the relationship

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut word_shift = E::Fr::one();
        for _ in 0..64 {
            word_shift.double();
        }

        let mut minus_word_shift = word_shift;
        minus_word_shift.negate();

        let mut minus_two_word_shift = word_shift;
        for _ in 0..64 {
            minus_two_word_shift.double();
        }
        minus_two_word_shift.negate();

        // low and high parts

        let mut lc_low = LinearCombination::zero();
        lc_low.add_assign_number_with_coeff(&self.inner[0].inner, E::Fr::one());
        lc_low.add_assign_number_with_coeff(&self.inner[1].inner, word_shift);
        lc_low.add_assign_number_with_coeff(&other.inner[0].inner, E::Fr::one());
        lc_low.add_assign_number_with_coeff(&other.inner[1].inner, word_shift);
        lc_low.add_assign_number_with_coeff(&result.inner[0].inner, minus_one);
        lc_low.add_assign_number_with_coeff(&result.inner[1].inner, minus_word_shift);
        lc_low.add_assign_boolean_with_coeff(&intermediate_of, minus_two_word_shift);
        lc_low.enforce_zero(cs)?;

        let mut lc_high = LinearCombination::zero();
        lc_high.add_assign_number_with_coeff(&self.inner[2].inner, E::Fr::one());
        lc_high.add_assign_number_with_coeff(&self.inner[3].inner, word_shift);
        lc_high.add_assign_number_with_coeff(&other.inner[2].inner, E::Fr::one());
        lc_high.add_assign_number_with_coeff(&other.inner[3].inner, word_shift);
        lc_high.add_assign_number_with_coeff(&result.inner[2].inner, minus_one);
        lc_high.add_assign_number_with_coeff(&result.inner[3].inner, minus_word_shift);
        lc_high.add_assign_boolean_with_coeff(&intermediate_of, E::Fr::one());
        lc_high.add_assign_boolean_with_coeff(&overflow, minus_two_word_shift);
        lc_high.enforce_zero(cs)?;

        Ok((result, overflow))
    }

    pub fn sub<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(Self, Boolean), SynthesisError> {
        let (result, underflow) = UInt256::make_witness_for_subtraction(self, other);
        let result = Self::alloc_from_biguint(cs, result)?;
        let underflow = Boolean::alloc(cs, underflow)?;

        let intermediate_uf_witness = match (self.get_value(), other.get_value()) {
            (Some(a), Some(b)) => {
                let modulus = BigUint::from(1u64) << 128u32;
                let of = (modulus.clone() + (a % &modulus) - (b % &modulus)) >> 128u8;

                use num_traits::Zero;
                Some(of.is_zero())
            }
            _ => None,
        };

        let intermediate_uf = Boolean::alloc(cs, intermediate_uf_witness)?;

        // enforce the relationship

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut word_shift = E::Fr::one();
        for _ in 0..64 {
            word_shift.double();
        }

        let mut two_word_shift = word_shift;
        for _ in 0..64 {
            two_word_shift.double();
        }

        let mut minus_word_shift = word_shift;
        minus_word_shift.negate();

        let mut minus_two_word_shift = two_word_shift;
        minus_two_word_shift.negate();

        // low and high parts

        let mut lc_low = LinearCombination::zero();
        lc_low.add_assign_number_with_coeff(&self.inner[0].inner, E::Fr::one());
        lc_low.add_assign_number_with_coeff(&self.inner[1].inner, word_shift);
        lc_low.add_assign_number_with_coeff(&other.inner[0].inner, minus_one);
        lc_low.add_assign_number_with_coeff(&other.inner[1].inner, minus_word_shift);
        lc_low.add_assign_number_with_coeff(&result.inner[0].inner, minus_one);
        lc_low.add_assign_number_with_coeff(&result.inner[1].inner, minus_word_shift);
        lc_low.add_assign_boolean_with_coeff(&intermediate_uf, two_word_shift);
        lc_low.enforce_zero(cs)?;

        let mut lc_high = LinearCombination::zero();
        lc_high.add_assign_number_with_coeff(&self.inner[2].inner, E::Fr::one());
        lc_high.add_assign_number_with_coeff(&self.inner[3].inner, word_shift);
        lc_high.add_assign_number_with_coeff(&other.inner[2].inner, minus_one);
        lc_high.add_assign_number_with_coeff(&other.inner[3].inner, minus_word_shift);
        lc_high.add_assign_number_with_coeff(&result.inner[2].inner, minus_one);
        lc_high.add_assign_number_with_coeff(&result.inner[3].inner, minus_word_shift);
        lc_high.add_assign_boolean_with_coeff(&intermediate_uf, minus_one);
        lc_high.add_assign_boolean_with_coeff(&underflow, two_word_shift);
        lc_high.enforce_zero(cs)?;

        Ok((result, underflow))
    }

    pub fn from_be_bytes_fixed<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bytes: &[Byte<E>; 32],
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::zero();
        let shifts = compute_shifts::<E::Fr>();
        for (chunk, dst) in bytes.chunks(8).zip(new.inner.iter_mut().rev()) {
            let mut lc = LinearCombination::zero();
            let mut shift = 0;
            for b in chunk.iter().rev() {
                lc.add_assign_number_with_coeff(&b.inner, shifts[shift]);
                shift += 8;
            }
            let num = lc.into_num(cs)?;
            *dst = UInt64::from_num_unchecked(num);
        }

        Ok(new)
    }

    pub fn from_le_bytes_fixed<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bytes: &[Byte<E>; 32],
    ) -> Result<Self, SynthesisError> {
        let mut input = bytes.to_vec();
        input.reverse();
        let input = input.try_into().unwrap();
        Self::from_be_bytes_fixed(cs, &input)
    }
}
