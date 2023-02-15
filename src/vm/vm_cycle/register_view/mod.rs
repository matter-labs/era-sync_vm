use super::*;
use cs_derive::*;
use crate::traits::*;


#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable, CSVariableLengthEncodable)]
#[derivative(Clone(bound = ""), Copy(bound = ""), Debug)]
pub struct Register<E: Engine>{
    pub inner: [UInt128<E>; 2]
}

impl<E: Engine> Default for Register<E> {
    fn default() -> Self {
        Register::zero()
    }
}

impl<E: Engine> Register<E> {
    pub fn is_constant(&self) -> bool {
        self.inner.iter().all(|el| el.inner.is_constant())
    }

    pub fn zero() -> Self {
        Register { inner: [UInt128::zero(); 2] }
    }

    pub fn from_imm(imm: UInt16<E>) -> Self {
        Register { inner: [UInt128::from_num_unchecked(imm.inner), UInt128::zero()] }
    }

    pub fn unsafe_multiselection_using_linear_combination<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        mask: &[Boolean],
        values: &[Self],
    ) -> Result<Self, SynthesisError> {
        unreachable!();
        assert_eq!(mask.len(), values.len());
        //assert!(mask.len() > 0);
        let mut new = Self::zero();
        for limb_idx in 0..2 {
            let limbs: Vec<_> = values.iter().map(|el| el.inner[limb_idx]).collect();
            let selected =
                UInt128::unsafe_multiselection_using_linear_combination(cs, mask, &limbs)?;
            new.inner[limb_idx] = selected;
        }

        Ok(new)
    }

    pub fn conditionally_reverse<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        condition_flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<(Self, Self), SynthesisError> {
        if CircuitEq::eq(a, b) {
            // no-op
            return Ok((a.clone(), b.clone()));
        }

        let (mut result_left, mut result_right) = (Self::zero(), Self::zero());
        for (((a, b), dst_left), dst_right) in a
            .inner
            .iter()
            .zip(b.inner.iter())
            .zip(result_left.inner.iter_mut())
            .zip(result_right.inner.iter_mut())
        {
            let (x, y) = UInt128::conditionally_reverse(cs, condition_flag, &a, &b)?;
            *dst_left = x;
            *dst_right = y;
        }

        Ok((result_left, result_right))
    }

    pub fn get_value(&self) -> Option<BigUint> {
        let mut base = BigUint::from(0u64);
        let mut shift = 0u32;
        for chunk in self.inner.iter() {
            if let Some(v) = chunk.get_value() {
                base += BigUint::from(v) << shift;
                shift += 128;
            } else {
                return None;
            }
        }

        Some(base)
    }

    pub fn get_partial_view(&self) -> RegisterInputView<E> {
        RegisterInputView {
            u8x32_view: None,
            u32x8_view: None,
            // lowest16: None,
            // lowest32: None,
            lowest160: None,
            decomposed_lowest160: None,
            // decomposed_lowest64: None,
            u64x4_view: None,
            u128x2_view: Some(self.inner.clone()),
        }
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS, a: &Self, b: &Self,
    ) -> Result<Boolean, SynthesisError> 
    {
        let t0 = UInt128::equals(cs, &a.inner[0], &b.inner[0])?;
        let t1 = UInt128::equals(cs, &a.inner[1], &b.inner[1])?;
        let eq = Boolean::and(cs, &t0, &t1)?;

        Ok(eq)
    }

    pub fn mask<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        mask: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::zero();
        for limb_idx in 0..2 {
            new.inner[limb_idx] = self.inner[limb_idx].mask(cs, mask)?;
        }

        Ok(new)
    }
}


#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct RegisterInputView<E: Engine>{
    // used for bitwise operations and as a shift
    pub u8x32_view: Option<[UInt8<E>; 32]>,
    // used only for the second operand - contract address
    pub lowest160: Option<UInt160<E>>,
    pub decomposed_lowest160: Option<(UInt64<E>, UInt64<E>, UInt32<E>)>,
    // pub decomposed_lowest64: Option<(UInt32<E>, UInt16<E>, UInt16<E>)>, 
    // used for multiplication/division
    pub u32x8_view: Option<[UInt32<E>; 8]>,
    pub u64x4_view: Option<[UInt64<E>; 4]>,
    pub u128x2_view: Option<[UInt128<E>; 2]>,
}

impl<E: Engine> RegisterInputView<E> {
    pub fn uninitialized() -> Self {
        RegisterInputView {
            u8x32_view: None,
            lowest160: None,
            decomposed_lowest160: None,
            // decomposed_lowest64: None,
            u32x8_view: None,
            u64x4_view: None,
            u128x2_view: None,
        }
    }

    pub fn get_value(&self) -> Option<BigUint> {
        let mut base = BigUint::from(0u64);
        let mut shift = 0u32;
        for chunk in self.u128x2_view.unwrap().iter() {
            if let Some(v) = chunk.get_value() {
                base += BigUint::from(v) << shift;
                shift += 128;
            } else {
                return None;
            }
        }

        Some(base)
    }

    pub fn from_input_value<CS>(cs: &mut CS, value: &Register<E>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        use num_traits::ToPrimitive;
        use std::convert::TryInto;

        if value.is_constant() {
            todo!();
        } else {
            let low_value = value.inner[0].get_value().map(|el| BigUint::from(el));
            let high_value = value.inner[1].get_value().map(|el| BigUint::from(el));

            let low_chunks = split_some_into_fixed_number_of_limbs(low_value, 8, 16);
            let high_chunks = split_some_into_fixed_number_of_limbs(high_value, 8, 16);

            let mut chunks = vec![];
            for c in low_chunks.into_iter().chain(high_chunks) {
                let c_value = c.map(|el| el.to_u8().unwrap());
                let u8_chunk = UInt8::allocate_unchecked(cs, c_value)?;
                chunks.push(u8_chunk);
            }
            let u8x32_view: [UInt8<E>; 32] = chunks.try_into().unwrap();

            let shifts = compute_shifts::<E::Fr>();

            let mut u32x8_view = vec![];
            let step = 8;
            for c in u8x32_view.chunks(4) {
                let mut lc = LinearCombination::zero();
                let mut shift = 0;
                for c in c.iter() {
                    lc.add_assign_number_with_coeff(&c.inner, shifts[shift]);
                    shift += step;
                }
                let el = lc.into_num(cs)?;
                u32x8_view.push(UInt32::from_num_unchecked(el));
            }

            let u32x8_view: [UInt32<E>; 8] = u32x8_view.try_into().unwrap();

            // let mut lc = LinearCombination::zero();
            // lc.add_assign_number_with_coeff(&u8x32_view[0].inner, shifts[0]);
            // lc.add_assign_number_with_coeff(&u8x32_view[1].inner, shifts[8]);
            // let lowest16 = lc.into_num(cs)?;
            // let lowest16 = UInt16::from_num_unchecked(lowest16);

            // let mut lc = LinearCombination::zero();
            // lc.add_assign_number_with_coeff(&lowest16.inner, shifts[0]);
            // lc.add_assign_number_with_coeff(&u8x32_view[2].inner, shifts[16]);
            // lc.add_assign_number_with_coeff(&u8x32_view[3].inner, shifts[24]);
            // let lowest32 = lc.into_num(cs)?;
            // let lowest32 = UInt32::from_num_unchecked(lowest32);

            // let mut lc = LinearCombination::zero();
            // lc.add_assign_number_with_coeff(&u8x32_view[4].inner, shifts[0]);
            // lc.add_assign_number_with_coeff(&u8x32_view[5].inner, shifts[8]);
            // let lowest16_02 = lc.into_num(cs)?;
            // let lowest16_02 = UInt16::from_num_unchecked(lowest16_02);

            // let mut lc = LinearCombination::zero();
            // lc.add_assign_number_with_coeff(&u8x32_view[6].inner, shifts[0]);
            // lc.add_assign_number_with_coeff(&u8x32_view[7].inner, shifts[8]);
            // let lowest16_03 = lc.into_num(cs)?;
            // let lowest16_03 = UInt16::from_num_unchecked(lowest16_03);

            // let mut lc = LinearCombination::zero();
            // lc.add_assign_number_with_coeff(&lowest32.inner, shifts[0]);
            // lc.add_assign_number_with_coeff(&lowest16_02.inner, shifts[32]);
            // lc.add_assign_number_with_coeff(&lowest16_03.inner, shifts[48]);
            // let lowest64 = lc.into_num(cs)?;
            // let lowest64 = UInt64::from_num_unchecked(lowest64);
            // let decomposed_lowest64 = (lowest32, lowest16_02, lowest16_03);

            // let mut u64x4_view = vec![lowest64.clone()];
            // // add limbs 1
            // let step = 8;
            // for c in u8x32_view.chunks(8).skip(1).take(1) {
            //     let mut lc = LinearCombination::zero();
            //     let mut shift = 0;
            //     for c in c.iter() {
            //         lc.add_assign_number_with_coeff(&c.inner, shifts[shift]);
            //         shift += step;
            //     }
            //     let el = lc.into_num(cs)?;
            //     u64x4_view.push(UInt64::from_num_unchecked(el));
            // }

            let mut u64x4_view = vec![];
            let step = 32;
            for c in u32x8_view.chunks(2) {
                let mut lc = LinearCombination::zero();
                let mut shift = 0;
                for c in c.iter() {
                    lc.add_assign_number_with_coeff(&c.inner, shifts[shift]);
                    shift += step;
                }
                let el = lc.into_num(cs)?;
                u64x4_view.push(UInt64::from_num_unchecked(el));
            }

            // // decompose 3rd limb
            // let mut lc = LinearCombination::zero();
            // lc.add_assign_number_with_coeff(&u8x32_view[16].inner, shifts[0]);
            // lc.add_assign_number_with_coeff(&u8x32_view[17].inner, shifts[8]);
            // lc.add_assign_number_with_coeff(&u8x32_view[18].inner, shifts[16]);
            // lc.add_assign_number_with_coeff(&u8x32_view[19].inner, shifts[24]);
            // let lowest32_20 = lc.into_num(cs)?;
            // let lowest32_20 = UInt32::from_num_unchecked(lowest32_20);

            // let mut lc = LinearCombination::zero();
            // lc.add_assign_number_with_coeff(&lowest32_20.inner, shifts[0]);
            // lc.add_assign_number_with_coeff(&u8x32_view[20].inner, shifts[32]);
            // lc.add_assign_number_with_coeff(&u8x32_view[21].inner, shifts[40]);
            // lc.add_assign_number_with_coeff(&u8x32_view[22].inner, shifts[48]);
            // lc.add_assign_number_with_coeff(&u8x32_view[23].inner, shifts[56]);
            // let u64_2 = lc.into_num(cs)?;
            // let u64_2 = UInt64::from_num_unchecked(u64_2);
            // u64x4_view.push(u64_2);

            // // finish with 4-th limb
            // for c in u8x32_view.chunks(8).skip(3) {
            //     let mut lc = LinearCombination::zero();
            //     let mut shift = 0;
            //     for c in c.iter() {
            //         lc.add_assign_number_with_coeff(&c.inner, shifts[shift]);
            //         shift += step;
            //     }
            //     let el = lc.into_num(cs)?;
            //     u64x4_view.push(UInt64::from_num_unchecked(el));
            // }
            let u64x4_view: [UInt64<E>; 4] = u64x4_view.try_into().unwrap();

            let mut minus_one = E::Fr::one();
            minus_one.negate();
            // enforce equality
            let step = 64;
            for (i, c) in u64x4_view.chunks(2).enumerate() {
                let mut lc = LinearCombination::zero();
                let mut shift = 0;
                for c in c.iter() {
                    lc.add_assign_number_with_coeff(&c.inner, shifts[shift]);
                    shift += step;
                }
                lc.add_assign_number_with_coeff(&value.inner[i].inner, minus_one);
                lc.enforce_zero(cs)?;
            }
            let u128x2_view = value.inner;

            let lowest32_20 = u32x8_view[4];

            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&u128x2_view[0].inner, shifts[0]);
            lc.add_assign_number_with_coeff(&lowest32_20.inner, shifts[128]);
            let lowest160 = lc.into_num(cs)?;
            let lowest160 = UInt160::from_num_unchecked(lowest160);
            let decomposed_lowest160 = (u64x4_view[0].clone(), u64x4_view[1].clone(), lowest32_20);

            let new = Self {
                u8x32_view: Some(u8x32_view),
                u32x8_view: Some(u32x8_view),
                // lowest16: Some(lowest16),
                // lowest32: Some(lowest32),
                lowest160: Some(lowest160),
                decomposed_lowest160: Some(decomposed_lowest160),
                // decomposed_lowest64: Some(decomposed_lowest64),
                u64x4_view: Some(u64x4_view),
                u128x2_view: Some(u128x2_view),
            };

            Ok(new)
        }
    }
}
