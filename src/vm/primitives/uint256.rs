use super::super::optimizer::OptimizationContext;
use super::super::partitioner::smart_and;
use super::structural_eq::*;
use super::*;
use franklin_crypto::plonk::circuit::bigint::bigint::*;
use franklin_crypto::plonk::circuit::bigint::*;
use num_traits::ToPrimitive;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct UInt256<E: Engine> {
    pub(crate) inner: [UInt64<E>; 4],
}

impl<E: Engine> Copy for UInt256<E> {}

impl<E: Engine> From<UInt64<E>> for UInt256<E> {
    fn from(x: UInt64<E>) -> Self {
        UInt256 {
            inner: [x, UInt64::zero(), UInt64::zero(), UInt64::zero()],
        }
    }
}

impl<E: Engine> CircuitEq<E> for UInt256<E> {
    fn eq(&self, other: &Self) -> bool {
        self.inner
            .iter()
            .zip(other.inner.iter())
            .all(|(a, b)| a.eq(b))
    }
}

impl<E: Engine> CircuitOrd<E> for UInt256<E> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for (a, b) in self.inner.iter().rev().zip(other.inner.iter().rev()) {
            match a.cmp(&b) {
                std::cmp::Ordering::Less => return std::cmp::Ordering::Less,
                std::cmp::Ordering::Greater => return std::cmp::Ordering::Greater,
                _ => {}
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl<E: Engine> CircuitSelectable<E> for UInt256<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        let inner0 = UInt64::conditionally_select(cs, flag, &a.inner[0], &b.inner[0])?;
        let inner1 = UInt64::conditionally_select(cs, flag, &a.inner[1], &b.inner[1])?;
        let inner2 = UInt64::conditionally_select(cs, flag, &a.inner[2], &b.inner[2])?;
        let inner3 = UInt64::conditionally_select(cs, flag, &a.inner[3], &b.inner[3])?;

        let res = UInt256 {
            inner: [inner0, inner1, inner2, inner3],
        };
        Ok(res)
    }
}

impl<E: Engine> CircuitOrthogonalSelectable<E> for UInt256<E> {
    fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        reference: Self,
        candidates: &[(Boolean, Self)],
    ) -> Result<Self, SynthesisError> {
        let reference = [
            reference.inner[0].clone(),
            reference.inner[1].clone(),
            reference.inner[2].clone(),
            reference.inner[3].clone(),
        ];
        let candidates: Vec<_> = candidates
            .iter()
            .map(|el| {
                let chunks = [
                    el.1.inner[0].clone(),
                    el.1.inner[1].clone(),
                    el.1.inner[2].clone(),
                    el.1.inner[3].clone(),
                ];
                (el.0, chunks)
            })
            .collect();

        let selected_chunks = array_select_update_assuming_orthogonality_per_full_array_strategy::<
            E,
            CS,
            UInt64<E>,
            4,
        >(cs, reference, &candidates)?;

        Ok(Self {
            inner: selected_chunks,
        })
    }
}

impl<E: Engine> Default for UInt256<E> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<E: Engine> UInt256<E> {
    pub fn zero() -> Self {
        Self {
            inner: [UInt64 {
                inner: Num::Constant(E::Fr::zero()),
            }; 4],
        }
    }

    pub fn one() -> Self {
        Self {
            inner: [
                UInt64 {
                    inner: Num::Constant(E::Fr::one()),
                },
                UInt64 {
                    inner: Num::Constant(E::Fr::zero()),
                },
                UInt64 {
                    inner: Num::Constant(E::Fr::zero()),
                },
                UInt64 {
                    inner: Num::Constant(E::Fr::zero()),
                },
            ],
        }
    }

    pub fn constant(value: BigUint) -> Self {
        let slices = split_some_into_fixed_number_of_limbs(Some(value), 64, 4);
        let mut new = Self::zero();

        for (i, el) in slices.into_iter().enumerate() {
            let value = el.unwrap().to_u64().unwrap();
            new.inner[i] = UInt64::from_uint(value);
        }
        new
    }

    pub fn allocate_in_optimization_context_with_applicability<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        ctx: &mut OptimizationContext<E>,
        applies: Boolean,
        marker: CtxMarker,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        for (i, el) in slices.into_iter().enumerate() {
            let value = el.map(|el| el.to_u64().unwrap());
            new.inner[i] = UInt64::allocate_in_optimization_context_with_applicability(
                cs, value, ctx, applies, marker,
            )?;
        }

        Ok(new)
    }

    pub fn canonical_from_num<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        num: &Num<E>,
    ) -> Result<Self, SynthesisError> {
        let value = num.get_value().map(|el| fe_to_biguint(&el));
        let limbs = split_some_into_fixed_number_of_limbs(value, 64, 4);
        assert_eq!(limbs.len(), 4);
        let mut new = Self::zero();
        for (i, value) in limbs.into_iter().enumerate() {
            let value = value.map(|el| el.to_u64().unwrap());
            let tmp = UInt64::allocate(cs, value)?;

            new.inner[i] = tmp;
        }

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&new.inner[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&new.inner[1].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&new.inner[2].inner, shifts[128]);
        lc.add_assign_number_with_coeff(&new.inner[3].inner, shifts[192]);
        lc.add_assign_number_with_coeff(&num, minus_one);
        lc.enforce_zero(cs)?;

        let mut char = repr_to_biguint::<E::Fr>(&E::Fr::char());
        char -= BigUint::from(1u64);

        use num_integer::Integer;

        let sh_128 = BigUint::from(1u64) << 128;

        let (c_high, c_low) = char.div_rem(&sh_128);
        let c_high_num = Num::Constant(biguint_to_fe(c_high.clone()));
        let c_low_num = Num::Constant(biguint_to_fe(c_low.clone()));

        // long sub
        let (wit, borrow) = match (new.inner[0].get_value(), new.inner[1].get_value()) {
            (Some(low), Some(high)) => {
                use num_traits::Zero;

                let tmp: BigUint =
                    sh_128.clone() + c_low - (BigUint::from(high) << 64) - BigUint::from(low);

                let (q, r) = tmp.div_rem(&sh_128);

                let borrow = q.is_zero();
                let wit = biguint_to_fe(r);

                (Some(wit), Some(borrow))
            }
            _ => (None, None),
        };

        let borrow = Boolean::alloc(cs, borrow)?;

        let tmp = Num::alloc(cs, wit)?;
        constraint_bit_length(cs, &tmp, 128)?;

        let mut minus_sh_64 = shifts[64];
        minus_sh_64.negate();

        // 2^128 * borrow + c_low - l0 - 2^64 * l1 - result = 0;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&c_low_num, shifts[0]);
        lc.add_assign_number_with_coeff(&new.inner[0].inner, minus_one);
        lc.add_assign_number_with_coeff(&new.inner[1].inner, minus_sh_64);
        lc.add_assign_boolean_with_coeff(&borrow, shifts[128]);
        lc.add_assign_number_with_coeff(&tmp, minus_one);
        lc.enforce_zero(cs)?;

        let wit = match (
            new.inner[2].get_value(),
            new.inner[3].get_value(),
            borrow.get_value(),
        ) {
            (Some(low), Some(high), Some(borrow)) => {
                use num_traits::Zero;

                let tmp: BigUint = c_high
                    - (BigUint::from(high) << 64)
                    - BigUint::from(low)
                    - BigUint::from(borrow as u64);
                let wit: E::Fr = biguint_to_fe(tmp);

                Some(wit)
            }
            _ => None,
        };

        let tmp = Num::alloc(cs, wit)?;
        constraint_bit_length(cs, &tmp, 128)?;

        // c_high - l2 - 2^64 * l3 - borrow - result = 0;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&c_high_num, shifts[0]);
        lc.add_assign_number_with_coeff(&new.inner[2].inner, minus_one);
        lc.add_assign_number_with_coeff(&new.inner[3].inner, minus_sh_64);
        lc.add_assign_boolean_with_coeff(&borrow, minus_one);
        lc.add_assign_number_with_coeff(&tmp, minus_one);
        lc.enforce_zero(cs)?;

        Ok(new)
    }

    pub fn get_value(&self) -> Option<BigUint> {
        let mut base = BigUint::from(0u64);
        let mut shift = 0u32;
        for chunk in self.inner.iter() {
            if let Some(v) = chunk.get_value() {
                base += BigUint::from(v) << shift;
                shift += 64;
            } else {
                return None;
            }
        }

        Some(base)
    }

    pub fn to_num_unchecked<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Num<E>, SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.inner[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.inner[1].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.inner[2].inner, shifts[128]);
        lc.add_assign_number_with_coeff(&self.inner[3].inner, shifts[192]);
        let num = lc.into_num(cs)?;

        Ok(num)
    }

    pub fn is_constant(&self) -> bool {
        self.inner.iter().all(|el| el.inner.is_constant())
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        condition_flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        if CircuitEq::eq(a, b) {
            // no-op
            return Ok(a.clone());
        }
        let mut result = Self::zero();
        for ((a, b), dst) in a
            .inner
            .iter()
            .zip(b.inner.iter())
            .zip(result.inner.iter_mut())
        {
            *dst = UInt64::conditionally_select(cs, condition_flag, &a, &b)?;
        }

        Ok(result)
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
            let (x, y) = UInt64::conditionally_reverse(cs, condition_flag, &a, &b)?;
            *dst_left = x;
            *dst_right = y;
        }

        Ok((result_left, result_right))
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let mut flags = vec![];
        let mut shift_64 = E::Fr::one();
        for _ in 0..64 {
            shift_64.double();
        }
        for pair in self.inner.chunks(2) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&pair[0].inner, E::Fr::one());
            lc.add_assign_number_with_coeff(&pair[1].inner, shift_64);
            let as_num = lc.into_num(cs)?;
            flags.push(as_num.is_zero(cs)?);
        }

        smart_and(cs, &flags)
    }

    /// only used in a specialized functions, like construction of the add/sub/div/mul witness
    #[track_caller]
    pub fn alloc_unchecked_from_biguint<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            new.inner[i] = UInt64 { inner: allocated };
        }

        Ok(new)
    }

    pub fn get_is_zero_witness<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError> {
        let mut witness = None;
        for l in self.inner.iter() {
            if let Some(v) = l.get_value() {
                if let Some(w) = witness.as_mut() {
                    *w = *w & (v == 0);
                } else {
                    witness = Some(v == 0);
                }
            } else {
                witness = None;
            }
        }

        let witness = Boolean::from(AllocatedBit::alloc(cs, witness)?);

        Ok(witness)
    }

    #[track_caller]
    pub fn constant_from_biguint(value: BigUint) -> Self {
        let slices = split_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        for (i, value) in slices.into_iter().enumerate() {
            let fe = biguint_to_fe::<E::Fr>(value);
            let constant = Num::Constant(fe);
            new.inner[i] = UInt64 { inner: constant };
        }

        new
    }

    #[track_caller]
    pub fn alloc_from_biguint<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            constraint_bit_length(cs, &allocated, 64)?;
            new.inner[i] = UInt64 { inner: allocated };
        }

        Ok(new)
    }

    #[track_caller]
    pub fn alloc_from_biguint_and_return_u16_chunks<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
    ) -> Result<(Self, [Num<E>; 16]), SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        let mut chunks = vec![];
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            let subchunks = constraint_bit_length(cs, &allocated, 64)?;
            chunks.extend(subchunks);
            new.inner[i] = UInt64 { inner: allocated };
        }

        let chunks: [_; 16] = chunks.try_into().unwrap();

        Ok((new, chunks))
    }

    #[track_caller]
    pub fn alloc_from_biguint_and_return_u8_chunks<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
    ) -> Result<(Self, [Num<E>; 32]), SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        let mut chunks = vec![];
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            let subchunks = constraint_bit_length_assuming_8x8_table(cs, &allocated, 64)?;
            chunks.extend(subchunks);
            new.inner[i] = UInt64 { inner: allocated };
        }

        let chunks: [_; 32] = chunks.try_into().unwrap();

        Ok((new, chunks))
    }

    /// perform mod 2^256 multiplication
    pub fn mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<[Self; 4], SynthesisError> {
        assert!(!self.is_constant());
        assert!(!other.is_constant());
        // we do schoolbook short multiplication, with some manual optimizations assuming length of the field

        // what looks optimal is to fit as many limbs as possible to fill 2^193 without overflow,
        // that means 2 limbs can be computed immediatelly, and then deal with the 3rd and 4th one

        // we can only accumulate 1 multiplication per gate, so we will have to manually write a trace here
        use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;
        assert_eq!(CS::Params::STATE_WIDTH, 4);
        use crate::bellman::plonk::better_better_cs::cs::{
            ArithmeticTerm, Gate, MainGate, MainGateTerm,
        };

        let next_term_range = CS::MainGate::range_of_next_step_linear_terms();
        assert_eq!(
            next_term_range.len(),
            1,
            "for now works only if only one variable is accessible on the next step"
        );

        let mut word_shift = E::Fr::one();
        for _ in 0..64 {
            word_shift.double();
        }

        let mut current_shift = word_shift;

        // limbs 0 and 1 of the target
        let mut previous = self.inner[0].inner.mul(cs, &other.inner[0].inner)?;

        for &(i, j) in [(0usize, 1usize), (1usize, 0usize)].iter() {
            let value = match (
                self.inner[i].inner.get_value(),
                other.inner[j].inner.get_value(),
                previous.get_value(),
            ) {
                (Some(a), Some(b), Some(c)) => {
                    let mut tmp = a;
                    tmp.mul_assign(&b);
                    tmp.mul_assign(&current_shift);
                    tmp.add_assign(&c);

                    Some(tmp)
                }
                _ => None,
            };

            let new_accumulator = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;

            let mut gate_term = MainGateTerm::<E>::new();
            let mul_term = ArithmeticTerm::from_variable_and_coeff(
                self.inner[i].inner.get_variable().get_variable(),
                current_shift,
            )
            .mul_by_variable(other.inner[j].inner.get_variable().get_variable());
            let previous_term =
                ArithmeticTerm::from_variable(previous.get_variable().get_variable());
            let new_term = ArithmeticTerm::from_variable(new_accumulator.get_variable());
            gate_term.add_assign(mul_term);
            gate_term.add_assign(previous_term);
            gate_term.sub_assign(new_term);

            cs.allocate_main_gate(gate_term)?;

            previous = Num::Variable(new_accumulator);
        }

        let width = [64, 64, 65];

        // in previous we have at maximum 192 bit number, so let's decompose it
        let chunks = split_some_into_limbs_of_variable_width(
            some_fe_to_biguint(&previous.get_value()),
            &width,
        );

        let mut allocated_limbs = vec![];
        for (chunk, &width) in chunks.into_iter().zip(width.iter()) {
            let allocated =
                AllocatedNum::alloc(cs, || Ok(*(some_biguint_to_fe::<E::Fr>(&chunk)).get()?))?;
            let allocated = Num::Variable(allocated);
            constraint_bit_length(cs, &allocated, width)?;
            allocated_limbs.push(allocated);
        }

        previous = allocated_limbs.pop().expect("must pop an element");

        // // now continue to the 3rd and 4th limbs
        // let mut lc = LinearCombination::zero();
        // lc.add_assign_number_with_coeff(&allocated_limbs.pop().unwrap(), E::Fr::one());
        // lc.add_assign_number_with_coeff(&last_short_chunk_allocated, word_shift);
        // previous = lc.into_num(cs)?;

        current_shift = E::Fr::one();

        // we need to place leftovers into 3rd and 4th limb, and continue the procedure
        for &(i, j) in [(0usize, 2usize), (2, 0), (1, 1)].iter() {
            // 2: a_i * b_j * 2^64 + accumulator -> accumulator

            let value = match (
                self.inner[i].inner.get_value(),
                other.inner[j].inner.get_value(),
                previous.get_value(),
            ) {
                (Some(a), Some(b), Some(c)) => {
                    let mut tmp = a;
                    tmp.mul_assign(&b);
                    tmp.mul_assign(&current_shift);
                    tmp.add_assign(&c);

                    Some(tmp)
                }
                _ => None,
            };

            let new_accumulator = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;

            let mut gate_term = MainGateTerm::<E>::new();
            let mul_term = ArithmeticTerm::from_variable_and_coeff(
                self.inner[i].inner.get_variable().get_variable(),
                current_shift,
            )
            .mul_by_variable(other.inner[j].inner.get_variable().get_variable());
            let previous_term =
                ArithmeticTerm::from_variable(previous.get_variable().get_variable());
            let new_term = ArithmeticTerm::from_variable(new_accumulator.get_variable());
            gate_term.add_assign(mul_term);
            gate_term.add_assign(previous_term);
            gate_term.sub_assign(new_term);

            cs.allocate_main_gate(gate_term)?;

            previous = Num::Variable(new_accumulator);
        }

        current_shift = word_shift;

        for &(i, j) in [(0usize, 3usize), (3, 0), (2, 1), (1, 2)].iter() {
            // 2: a_i * b_j * 2^64 + accumulator -> accumulator

            let value = match (
                self.inner[i].inner.get_value(),
                other.inner[j].inner.get_value(),
                previous.get_value(),
            ) {
                (Some(a), Some(b), Some(c)) => {
                    let mut tmp = a;
                    tmp.mul_assign(&b);
                    tmp.mul_assign(&current_shift);
                    tmp.add_assign(&c);

                    Some(tmp)
                }
                _ => None,
            };

            let new_accumulator = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;

            let mut gate_term = MainGateTerm::<E>::new();
            let mul_term = ArithmeticTerm::from_variable_and_coeff(
                self.inner[i].inner.get_variable().get_variable(),
                current_shift,
            )
            .mul_by_variable(other.inner[j].inner.get_variable().get_variable());
            let previous_term =
                ArithmeticTerm::from_variable(previous.get_variable().get_variable());
            let new_term = ArithmeticTerm::from_variable(new_accumulator.get_variable());
            gate_term.add_assign(mul_term);
            gate_term.add_assign(previous_term);
            gate_term.sub_assign(new_term);

            cs.allocate_main_gate(gate_term)?;

            previous = Num::Variable(new_accumulator);
        }

        let width = [64, 64, 66];

        // in previous we have at maximum 192 bit number, so let's decompose it
        let chunks = split_some_into_limbs_of_variable_width(
            some_fe_to_biguint(&previous.get_value()),
            &width,
        );

        for (chunk, &width) in chunks.into_iter().zip(width.iter()) {
            let allocated =
                AllocatedNum::alloc(cs, || Ok(*(some_biguint_to_fe::<E::Fr>(&chunk)).get()?))?;
            let allocated = Num::Variable(allocated);
            constraint_bit_length(cs, &allocated, width)?;
            allocated_limbs.push(allocated);
        }

        let mut new = Self::zero();

        for i in 0..4 {
            new.inner[i] = UInt64 {
                inner: allocated_limbs[i],
            };
        }

        // we return thing like a*b = c + d

        Ok([self.clone(), other.clone(), new, Self::zero()])
    }

    /// perform mod 2^512 multiplication
    pub fn full_mul<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<[Self; 5], SynthesisError> {
        assert!(!self.is_constant());
        assert!(!other.is_constant());
        // we do schoolbook short multiplication, with some manual optimizations assuming length of the field

        // what looks optimal is to fit as many limbs as possible to fill 2^193 without overflow,
        // that means 2 limbs can be computed immediatelly, and then deal with the 3rd and 4th one

        // we can only accumulate 1 multiplication per gate, so we will have to manually write a trace here

        use crate::bellman::plonk::better_better_cs::cs::{
            ArithmeticTerm, Gate, MainGate, MainGateTerm,
        };

        let mut word_shift = E::Fr::one();
        for _ in 0..64 {
            word_shift.double();
        }

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut allocated_limbs = vec![];
        let mut previous = self.inner[0].inner.mul(cs, &other.inner[0].inner)?;

        let sources = vec![
            vec![vec![(0usize, 1usize), (1, 0)]], // 0th and 1st limb
            vec![
                vec![(0usize, 2usize), (2, 0), (1, 1)],
                vec![(0usize, 3usize), (3, 0), (2, 1), (1, 2)],
            ], // limbs 2 and 3
            vec![
                vec![(1usize, 3usize), (3, 1), (2, 2)],
                vec![(2usize, 3usize), (3, 2)],
            ], //limbs 4 and 5
            vec![vec![(3usize, 3usize)]],         // limbs 6 and 7
        ];

        // let bit_widths = vec![
        //     vec![64, 64, 65],
        //     vec![64, 64, 67],
        //     vec![64, 64, 68],
        //     vec![64, 64],
        // ];

        // we may not care about particular high limb width
        let bit_widths = vec![
            vec![64, 64, 80],
            vec![64, 64, 80],
            vec![64, 64, 80],
            vec![64, 64],
        ];

        let shifts = vec![
            vec![word_shift],
            vec![E::Fr::one(), word_shift],
            vec![E::Fr::one(), word_shift],
            vec![E::Fr::one()],
        ];

        assert_eq!(sources.len(), bit_widths.len());
        assert_eq!(sources.len(), shifts.len());

        // limbs 2 and 3 of the target, propagating double carry to 4th, then 4 and 5 -> 6th, then 6 and 7
        for (round, ((source_limbs, width), shifts)) in sources
            .into_iter()
            .zip(bit_widths.into_iter())
            .zip(shifts.into_iter())
            .enumerate()
        {
            // perform additions
            assert_eq!(source_limbs.len(), shifts.len());
            let last_one = round == 3;
            for (source, current_shift) in source_limbs.into_iter().zip(shifts.into_iter()) {
                for (i, j) in source.into_iter() {
                    let value = match (
                        self.inner[i].inner.get_value(),
                        other.inner[j].inner.get_value(),
                        previous.get_value(),
                    ) {
                        (Some(a), Some(b), Some(c)) => {
                            let mut tmp = a;
                            tmp.mul_assign(&b);
                            tmp.mul_assign(&current_shift);
                            tmp.add_assign(&c);

                            Some(tmp)
                        }
                        _ => None,
                    };

                    let new_accumulator = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;

                    let mut gate_term = MainGateTerm::<E>::new();
                    let mul_term = ArithmeticTerm::from_variable_and_coeff(
                        self.inner[i].inner.get_variable().get_variable(),
                        current_shift,
                    )
                    .mul_by_variable(other.inner[j].inner.get_variable().get_variable());
                    let previous_term =
                        ArithmeticTerm::from_variable(previous.get_variable().get_variable());
                    let new_term = ArithmeticTerm::from_variable(new_accumulator.get_variable());
                    gate_term.add_assign(mul_term);
                    gate_term.add_assign(previous_term);
                    gate_term.sub_assign(new_term);

                    cs.allocate_main_gate(gate_term)?;

                    previous = Num::Variable(new_accumulator);
                }
            }

            dbg!(previous.get_value());

            let chunks = split_some_into_limbs_of_variable_width(
                some_fe_to_biguint(&previous.get_value()),
                &width,
            );

            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&previous, minus_one);

            let mut tmp = E::Fr::one();
            for (chunk, &width) in chunks.into_iter().zip(width.iter()) {
                let allocated =
                    AllocatedNum::alloc(cs, || Ok(*(some_biguint_to_fe::<E::Fr>(&chunk)).get()?))?;
                let allocated = Num::Variable(allocated);
                constraint_bit_length(cs, &allocated, width)?;
                lc.add_assign_number_with_coeff(&allocated, tmp);
                for _ in 0..width {
                    tmp.double();
                }
                allocated_limbs.push(allocated);
            }
            lc.enforce_zero(cs)?;

            if !last_one {
                previous = allocated_limbs.pop().expect("must pop");
            }
        }

        let mut low = Self::zero();
        let mut high = Self::zero();

        for i in 0..4 {
            low.inner[i] = UInt64 {
                inner: allocated_limbs[i],
            };
        }

        for i in 0..4 {
            high.inner[i] = UInt64 {
                inner: allocated_limbs[i + 4],
            };
        }

        // we return thing like a*b = c + d

        Ok([self.clone(), other.clone(), low, high, Self::zero()])
    }

    pub fn mask<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        mask: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::zero();
        for limb_idx in 0..4 {
            new.inner[limb_idx] = self.inner[limb_idx].mask(cs, mask)?;
        }

        Ok(new)
    }

    pub fn into_u128_pair<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[UInt128<E>; 2], SynthesisError> {
        let mut shift_64 = E::Fr::one();
        for _ in 0..64 {
            shift_64.double();
        }
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.inner[0].inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&self.inner[1].inner, shift_64);
        let low = lc.into_num(cs)?;
        let low = UInt128::from_num_unchecked(low);

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.inner[2].inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&self.inner[3].inner, shift_64);
        let high = lc.into_num(cs)?;
        let high = UInt128::from_num_unchecked(high);

        Ok([low, high])
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let a = a.into_u128_pair(cs)?;
        let b = b.into_u128_pair(cs)?;

        let t0 = UInt128::equals(cs, &a[0], &b[0])?;
        let t1 = UInt128::equals(cs, &a[1], &b[1])?;
        let eq = Boolean::and(cs, &t0, &t1)?;

        Ok(eq)
    }

    pub fn into_bits_le<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut result = vec![];
        for limb in self.inner.iter() {
            result.extend_from_slice(&limb.inner.into_bits_le(cs, Some(64))?);
        }
        assert_eq!(result.len(), 256);
        Ok(result)
    }

    pub fn restrict_to_uint160_unchecked<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<UInt160<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let res = if self.is_constant() {
            let value = u160 {
                limb0: self.inner[0].get_value().unwrap(),
                limb1: self.inner[1].get_value().unwrap(),
                limb2: self.inner[2].get_value().unwrap() as u32,
            };

            Ok(UInt160::from_uint(value))
        } else {
            let value = u160::from_fields_options(
                self.inner[0].get_value(),
                self.inner[1].get_value(),
                self.inner[2].get_value(),
            );
            UInt160::allocate(cs, value)
        };

        res
    }

    pub fn make_witness_for_addition(a: &Self, b: &Self) -> (Option<BigUint>, Option<bool>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                let result = a + b;
                let c = result.clone() % (BigUint::from(1u64) << 256);
                use num_traits::identities::Zero;
                let of = !(result >> 256u32).is_zero();
                (Some(c), Some(of))
            }
            _ => (None, None),
        }
    }

    pub fn make_witness_for_subtraction(a: &Self, b: &Self) -> (Option<BigUint>, Option<bool>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                let borrow = &a < &b;
                let mut result = BigUint::from(0u64);
                if borrow {
                    result += BigUint::from(1u64) << 256u32;
                }
                result += a;
                result -= b;
                (Some(result), Some(borrow))
            }
            _ => (None, None),
        }
    }

    pub fn make_witness_for_multiplication(
        a: &Self,
        b: &Self,
    ) -> (Option<BigUint>, Option<BigUint>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                let result = a * b;
                let low = result.clone() % (BigUint::from(1u64) << 256);
                let high = result >> 256u32;
                (Some(high), Some(low))
            }
            _ => (None, None),
        }
    }

    pub fn make_witness_for_division(a: &Self, b: &Self) -> (Option<BigUint>, Option<BigUint>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                use num_traits::Zero;
                if b.is_zero() {
                    (Some(BigUint::from(0u64)), Some(a))
                } else {
                    use num_integer::Integer;
                    let (q, r) = a.div_rem(&b);
                    (Some(q), Some(r))
                }
            }
            _ => (None, None),
        }
    }
}

impl<E: Engine> IntoBytes<E> for UInt256<E> {
    fn into_le_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let num_bytes = 32;

        let result = if self.is_constant() {
            let value = self.get_value().expect("must get a value for a constant");
            let mut result = value.to_bytes_le();
            result.resize(num_bytes, 0u8);

            let result: Vec<_> = result.into_iter().map(|el| Byte::constant(el)).collect();

            result
        } else {
            let mut result = vec![];
            for limb in self.inner.iter() {
                let encoding = limb.into_le_bytes(cs)?;
                result.extend(encoding);
            }

            result
        };

        assert_eq!(result.len(), num_bytes);

        Ok(result)
    }

    fn into_be_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}

impl<E: Engine> CircuitArithmeticEncodable<E> for UInt256<E> {
    fn encoding_length_is_constant() -> bool {
        true
    }

    fn encoding_length() -> usize {
        2
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let encoding = self.into_u128_pair(cs)?;

        let enc = vec![encoding[0].inner, encoding[1].inner];

        Ok(enc)
    }

    fn get_witness_value(&self) -> Option<Vec<E::Fr>> {
        None
    }
}

impl<E: Engine> CircuitArithmeticEncodableExt<E> for UInt256<E> {
    type Witness = BigUint;

    fn make_witness(&self) -> Option<Self::Witness> {
        self.get_value()
    }

    fn placeholder_witness() -> Self::Witness {
        BigUint::from(0u64)
    }
}

impl<E: Engine> CircuitArithmeticDecodableExt<E> for UInt256<E> {
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::alloc_from_biguint(cs, witness)?;
        let encoding = <Self as CircuitArithmeticEncodable<E>>::encode(&new, cs)?;

        for (enc, val) in encoding.into_iter().zip(values.iter()) {
            enc.enforce_equal(cs, val)?;
        }

        Ok(new)
    }

    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::alloc_from_biguint(cs, witness)?;
        let encoding = <Self as CircuitArithmeticEncodable<E>>::encode(&new, cs)?;

        let mut tmp = vec![];

        for (enc, val) in encoding.into_iter().zip(values.iter()) {
            let eq = Num::equals(cs, &enc, val)?;
            tmp.push(eq);
        }

        let eq = smart_and(cs, &tmp)?;
        can_not_be_false_if_flagged(cs, &eq, should_execute)?;

        Ok(new)
    }
}

// impl<E: Engine> CircuitArithmeticCommitable<E> for UInt256<E> {}

use crate::traits::*;

impl<E: Engine> UInt256<E> {
    pub const CIRCUIT_ENCODING_LEN: usize = 2;
}

impl<E: Engine> CSPackable<E, 2> for UInt256<E> {
    fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        let encoding = self.into_u128_pair(cs)?;

        let enc = [encoding[0].inner, encoding[1].inner];

        Ok(enc)
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, 2> for UInt256<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        let encoding = self.into_u128_pair(cs)?;

        let enc = [encoding[0].inner, encoding[1].inner];

        Ok(enc)
    }
}

impl<E: Engine> CircuitVariableLengthEncodable<E> for UInt256<E> {
    fn encoding_length() -> usize {
        2
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let encoding = self.into_u128_pair(cs)?;

        let enc = vec![encoding[0].inner, encoding[1].inner];

        Ok(enc)
    }
}

impl<E: Engine> CSWitnessable<E> for UInt256<E> {
    type Witness = BigUint;
    fn create_witness(&self) -> Option<Self::Witness> {
        self.get_value()
    }
    fn placeholder_witness() -> Self::Witness {
        BigUint::from(0u64)
    }
}

impl<E: Engine> CSAllocatable<E> for UInt256<E> {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_biguint(cs, witness)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::*;
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::data_structures::alg_binary_tree::rescue_impl::StaticGenericBinaryTreeHasher;
    use crate::data_structures::SmallFixedWidthInteger as Integer;
    use crate::ff::*;
    use crate::pairing::bn256::{Bn256, Fr};
    use crate::testing::*;
    use crate::traits::GenericHasher;
    use crate::traits::*;
    use crate::utils::*;
    use rand::{Rng, SeedableRng, XorShiftRng};

    #[test]
    fn test_trivial_mul() {
        let (mut cs, _, _) = create_test_artifacts();
        inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 16).unwrap();

        let value: BigUint = (BigUint::from(1u64) << 256) - BigUint::from(1u64);

        let a = UInt256::alloc_from_biguint(&mut cs, Some(value.clone())).unwrap();
        println!("{} gates to allocate", cs.n());
        let b = UInt256::alloc_from_biguint(&mut cs, Some(value.clone())).unwrap();

        let n = cs.n();
        let [_aa, _bb, cc, _dd] = a.mul(&mut cs, &b).unwrap();

        let c: BigUint = (value.clone() * &value) % (BigUint::from(1u64) << 256);

        dbg!(c.to_str_radix(16));
        dbg!(cc.get_value().unwrap().to_str_radix(16));
        println!("{} gates to multiply", cs.n() - n);
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_full_mul() {
        let (mut cs, _, _) = create_test_artifacts();
        inscribe_default_range_table_for_bit_width_over_first_three_columns(&mut cs, 16).unwrap();

        let value: BigUint = (BigUint::from(1u64) << 256) - BigUint::from(1u64);

        let a = UInt256::alloc_from_biguint(&mut cs, Some(value.clone())).unwrap();
        println!("{} gates to allocate", cs.n());
        let b = UInt256::alloc_from_biguint(&mut cs, Some(value.clone())).unwrap();

        let n = cs.n();
        let [_aa, _bb, low, high, _dd] = a.full_mul(&mut cs, &b).unwrap();

        let low_value = low.get_value().unwrap();
        let high_value: BigUint = high.get_value().unwrap();

        let c: BigUint = value.clone().pow(2);

        let mut cc_value = low_value;
        cc_value += high_value << 256u32;

        assert_eq!(cc_value, c);
        println!("{} gates for 512b multiply", cs.n() - n);
        assert!(cs.is_satisfied());
    }
}
