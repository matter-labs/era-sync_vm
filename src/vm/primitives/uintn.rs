use super::*;
use super::super::structural_eq::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct UInt<E: Engine, const N: usize>{
    pub inner: Num<E>
}

impl<E: Engine, const N: usize> Copy for UInt<E, N> {}

impl<E: Engine, const N: usize> CircuitEq for UInt<E, N> {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<E: Engine, const N: usize> CircuitOrd for UInt<E, N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<E: Engine, const N: usize> UInt<E, N> {
    pub fn zero() -> Self {
        Self {inner: Num::Constant(E::Fr::zero())}
    }
    
    #[track_caller]
    pub fn constant(value: E::Fr) -> Result<Self, SynthesisError> {
        let width = value.into_repr().num_bits() as usize;
        if width > N {
            return Err(SynthesisError::Unsatisfiable);
        }
    
        let value = Num::Constant(value);
        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn allocate<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u128>) -> Result<Self, SynthesisError> {
        let value = value.map(|el| u128_to_fe(el));
        let allocated = AllocatedNum::alloc(
            cs,
            || {
                Ok(*value.get()?)
            }
        )?;
        let value = Num::Variable(allocated);
        constraint_bit_length(cs, &value, Self::WIDTH)?;
         
        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn from_witness_with_applicability<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u128>, ctx: &mut CTX<E>, applies: Boolean, marker: Marker) -> Result<Self, SynthesisError> {
        let value = value.map(|el| u128_to_fe(el));
        let allocated = AllocatedNum::alloc(
            cs,
            || {
                Ok(*value.get()?)
            }
        )?;
        let value = Num::Variable(allocated);
        ctx.add_range_check(&value, applies, marker, Self::WIDTH);

        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn from_witness<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u128>, ctx: &mut CTX<E>, marker: Marker) -> Result<Self, SynthesisError> {
        let value = value.map(|el| u128_to_fe(el));
        let allocated = AllocatedNum::alloc(
            cs,
            || {
                Ok(*value.get()?)
            }
        )?;
        let value = Num::Variable(allocated);
        ctx.add_unconditional_range_check(&value, marker, Self::WIDTH);

        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn from_witness_unchecked<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<u128>) -> Result<Self, SynthesisError> {
        let value = value.map(|el| u128_to_fe(el));
        let allocated = AllocatedNum::alloc(
            cs,
            || {
                Ok(*value.get()?)
            }
        )?;
        let value = Num::Variable(allocated);
        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn from_num_with_applicability(value: Num<E>, ctx: &mut CTX<E>, applies: Boolean, marker: Marker) -> Result<Self, SynthesisError> {
        ctx.add_range_check(&value, applies, marker, Self::WIDTH);

        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn from_num(value: Num<E>, ctx: &mut CTX<E>, marker: Marker) -> Result<Self, SynthesisError> {
        ctx.add_unconditional_range_check(&value, marker, Self::WIDTH);

        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn from_num_unchecked(value: Num<E>) -> Result<Self, SynthesisError> {
        let new = Self {
            inner: value,
        };

        Ok(new)
    }

    pub fn into_value(&self) -> Num<E> {
        self.inner.clone()
    }

    pub fn get_value(&self) -> Option<u128> {
        self.inner.get_value().map(|el| {
            let repr = el.into_repr();
            let value = (repr.as_ref()[0] as u128) + ((repr.as_ref()[1] as u128) << 64);
            for &limb in repr.as_ref()[2..].iter() {
                assert_eq!(limb, 0);
            }

            value
        })
    }

    pub fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(Self, Boolean), SynthesisError> {
        let (value_witness, of_witness) = match (self.get_value(), other.get_value()) {
            (Some(current), Some(other)) => {
                let (res, of) = current.overflowing_sub(other);

                (Some(res), Some(of))
            },
            _ => {
                (None, None)
            }
        };

        let result = Self::allocate(
            cs,
            value_witness
        )?;

        let new_of = Boolean::from(AllocatedBit::alloc(cs, of_witness)?);

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut shift = E::Fr::one();
        for _ in 0..Self::WIDTH {
            shift.double();
        }
        shift.negate();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&other.inner, minus_one);
        lc.add_assign_boolean_with_coeff(&new_of, shift);
        lc.add_assign_number_with_coeff(&result.inner, minus_one);

        lc.enforce_zero(cs)?;

        Ok((result, new_of))
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        condition_flag: &Boolean,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError> {
        if CircuitEq::eq(a, b) {
            // no-op
            return Ok(a.clone());
        }
        let new_value = Num::conditionally_select(cs, condition_flag, &a.inner, &b.inner)?;

        Ok(
            Self {
                inner: new_value,
            }
        )
    }

    pub fn from_boolean<CS: ConstraintSystem<E>>(cs: &mut CS, value: &Boolean) -> Result<Self, SynthesisError> {
        let num = Term::from_boolean(&value).collapse_into_num(cs)?;
        Ok(
            Self {
                inner: num
            }
        )
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self
    ) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &a.inner, &b.inner)
    }
}

impl<E: Engine, const N: usize> IntoBytes<E> for UInt<E, N> {
    fn into_le_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut num_bytes = 16;

        let result = match self.inner {
            Num::Variable(ref var) => {
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                let factor = E::Fr::from_str("256").unwrap();
                let mut coeff = E::Fr::one();
                let mut result = Vec::with_capacity(num_bytes);
                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self.inner, minus_one);
                let witness = split_some_into_slices(var.get_value(), 8, num_bytes);
                for w in witness.into_iter() {
                    let allocated = AllocatedNum::alloc(
                        cs,
                        || {
                            Ok(*w.get()?)
                        }
                    )?;
                    let num = Num::Variable(allocated);
                    let byte = Byte::from_num(cs, num.clone())?;
                    result.push(byte);

                    lc.add_assign_number_with_coeff(&num, coeff);
                    coeff.mul_assign(&factor);
                }

                lc.enforce_zero(cs)?;

                result
            },
            Num::Constant(constant) => {
                let mut result = Vec::with_capacity(num_bytes);
                let witness = split_into_slices(&constant, 8, num_bytes);
                for w in witness.into_iter() {
                    let num = Num::Constant(w);
                    let byte = Byte::from_num(cs, num)?;
                    result.push(byte);
                }

                result
            }
        };

        assert_eq!(result.len(), num_bytes);
        
        Ok(result)
    }

    fn into_be_bytes<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}