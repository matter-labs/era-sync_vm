use crate::bellman::SynthesisError;
use crate::data_structures::markers::*;
use crate::derivative::*;
use crate::ff::*;
use crate::pairing::*;
use crate::traits::CSAllocatable;
use crate::utils::*;
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::bigint::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::Assignment;
use num_bigint::*;

pub mod byte;
pub mod bytes32;
pub mod path_checks;
pub mod traits;
pub mod utils;

use franklin_crypto::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;

use self::utils::constraint_bit_length;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct SmallFixedWidthInteger<E: Engine, W: WidthMarker> {
    pub(crate) value: Num<E>,
    #[derivative(Debug = "ignore")]
    pub(crate) bits: Option<Vec<Boolean>>,
    #[derivative(Debug = "ignore")]
    pub(crate) _marker: std::marker::PhantomData<W>,
}

impl<E: Engine, W: WidthMarker> SmallFixedWidthInteger<E, W> {
    pub fn zero() -> Self {
        Self {
            value: Num::Constant(E::Fr::zero()),
            bits: None,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn constant(value: E::Fr) -> Result<Self, SynthesisError> {
        let width = value.into_repr().num_bits() as usize;
        if width > W::WIDTH {
            panic!("Constant is too large: {} for {} bits", value, W::WIDTH);
        }

        let value = Num::Constant(value);
        let new = Self {
            value: value,
            bits: None,
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    pub fn constant_from_u128(value: u128) -> Self {
        let width = (128u32 - value.leading_zeros()) as usize;
        if width > W::WIDTH {
            panic!("Constant is too large: {} for {} bits", value, W::WIDTH);
        }

        let value = Num::Constant(u128_to_fe(value));
        let new = Self {
            value: value,
            bits: None,
            _marker: std::marker::PhantomData,
        };

        new
    }

    pub fn from_le_bits<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        assert!(bits.len() <= W::WIDTH);
        let num = LinearCombination::uniquely_pack_le_booleans_into_single_num(cs, bits)?;
        let mut bits_padded = bits.to_vec();
        bits_padded.resize(W::WIDTH, Boolean::constant(false));

        let new = Self {
            value: num,
            bits: Some(bits_padded),
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    #[track_caller]
    pub fn allocate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<E::Fr>,
    ) -> Result<Self, SynthesisError> {
        let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
        let value = Num::Variable(allocated);
        constraint_bit_length(cs, &value, W::WIDTH)?;
        let new = Self {
            value: value,
            bits: None,
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    #[track_caller]
    pub fn allocate_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<E::Fr>,
    ) -> Result<Self, SynthesisError> {
        if let Some(v) = value.as_ref() {
            let num_bits = v.into_repr().num_bits();
            assert!(num_bits as usize <= W::WIDTH);
        }
        let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
        let value = Num::Variable(allocated);

        let new = Self {
            value: value,
            bits: None,
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    pub fn allocate_and_create_bits<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<E::Fr>,
        limit: Option<usize>,
    ) -> Result<Self, SynthesisError> {
        let limit = if let Some(limit) = limit {
            limit
        } else {
            W::WIDTH
        };

        let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
        let bits = allocated.into_bits_le(cs, Some(limit))?;
        let value = Num::Variable(allocated);
        let new = Self {
            value: value,
            bits: Some(bits),
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    #[track_caller]
    pub fn from_u32_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<u32>,
    ) -> Result<Self, SynthesisError> {
        let witness = if let Some(value) = value {
            let mut repr = E::Fr::zero().into_repr();
            repr.as_mut()[0] = value as u64;

            Some(E::Fr::from_repr(repr).unwrap())
        } else {
            None
        };

        Self::allocate(cs, witness)
    }

    #[track_caller]
    pub fn from_u128_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<u128>,
    ) -> Result<Self, SynthesisError> {
        let witness = if let Some(value) = value {
            Some(u128_to_fe(value))
        } else {
            None
        };

        Self::allocate(cs, witness)
    }

    #[track_caller]
    pub fn from_num<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Num<E>,
    ) -> Result<Self, SynthesisError> {
        constraint_bit_length(cs, &value, W::WIDTH)?;

        let new = Self {
            value: value,
            bits: None,
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    pub fn from_num_unchecked(value: Num<E>) -> Self {
        if let Some(value) = value.get_value() {
            let num_bits = value.into_repr().num_bits() as usize;
            assert!(num_bits <= W::WIDTH);
        }

        let new = Self {
            value: value,
            bits: None,
            _marker: std::marker::PhantomData,
        };

        new
    }

    #[track_caller]
    pub fn extend<WW: WidthMarker>(&self) -> Result<SmallFixedWidthInteger<E, WW>, SynthesisError> {
        if WW::WIDTH >= W::WIDTH {
            let mut new_bits = self.bits.clone();
            if let Some(bits) = new_bits.as_mut() {
                bits.resize(WW::WIDTH, Boolean::constant(false));
            }
            Ok(SmallFixedWidthInteger::<E, WW> {
                value: self.value.clone(),
                bits: new_bits,
                _marker: std::marker::PhantomData,
            })
        } else {
            Err(SynthesisError::Unsatisfiable)
        }
    }

    pub fn calculate_bits<CS: ConstraintSystem<E>>(
        &mut self,
        _cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        if let Some(bits) = self.bits.as_ref() {
            assert_eq!(bits.len(), W::WIDTH);
        } else {
            unimplemented!("NYI");
        }

        Ok(())
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.value.is_zero(cs)
    }

    pub fn get_bits(&self) -> Vec<Boolean> {
        self.bits
            .as_ref()
            .expect("bit must be calculated one way or another")
            .to_vec()
    }

    pub fn into_value(&self) -> Num<E> {
        self.value.clone()
    }

    pub fn speculative_add<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        to_add: &Self,
        execute: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let new_result_witness_value = match (
            self.value.get_value(),
            to_add.get_value(),
            execute.get_value(),
        ) {
            (Some(current), Some(to_add), Some(execute)) => {
                let mut new = current;
                if execute {
                    new.add_assign(&to_add);
                }

                Some(new)
            }
            _ => None,
        };

        // this will contait a range check
        let new_value = Self::allocate(cs, new_result_witness_value)?;

        let addition_result = self.value.add(cs, &to_add.into_value())?;

        let are_equal = Num::equals(cs, &addition_result, &new_value.value)?;

        // only forbidden combination is if we execute values are not equal
        let invalid = Boolean::and(cs, &are_equal.not(), &execute)?;
        Boolean::enforce_equal(cs, &invalid, &Boolean::constant(false))?;

        Ok(new_value)
    }

    /// Performs speculative subtraction with forbidden overflow of the intermediate result
    /// even we do nothing at the end
    pub fn speculative_sub<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        to_sub: &Self,
        execute: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let new_result_witness_value = match (
            self.value.get_value(),
            to_sub.get_value(),
            execute.get_value(),
        ) {
            (Some(current), Some(to_add), Some(execute)) => {
                let mut new = current;
                if execute {
                    new.sub_assign(&to_add);
                }

                Some(new)
            }
            _ => None,
        };

        // this will contait a range check
        let new_value = Self::allocate(cs, new_result_witness_value)?;

        let result = self.value.sub(cs, &to_sub.into_value())?;

        let are_equal = Num::equals(cs, &result, &new_value.value)?;

        // only forbidden combination is if we execute values are not equal
        let invalid = Boolean::and(cs, &are_equal.not(), &execute)?;
        Boolean::enforce_equal(cs, &invalid, &Boolean::constant(false))?;

        Ok(new_value)
    }

    /// Performs subtraction with borrow
    pub fn sub<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        to_sub: &Self,
    ) -> Result<(Self, Boolean), SynthesisError> {
        let (new_result_witness_value, of) = match (self.get_value(), to_sub.get_value()) {
            (Some(current), Some(to_sub)) => {
                use num_integer::Integer;
                use num_traits::Zero;

                let current = fe_to_biguint(&current);
                let to_sub = fe_to_biguint(&to_sub);
                let buffer = BigUint::from(1u64) << W::WIDTH;

                let result = buffer.clone() + current - to_sub;
                let (q, r) = result.div_rem(&buffer);
                let borrow = q.is_zero();

                let wit = biguint_to_fe(r);

                (Some(wit), Some(borrow))
            }
            _ => (None, None),
        };

        // this will contait a range check
        let new_value = Self::allocate(cs, new_result_witness_value)?;

        let of = Boolean::alloc(cs, of)?;

        let mut shift = E::Fr::one();
        for _ in 0..W::WIDTH {
            shift.double();
        }

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.value, E::Fr::one());
        lc.add_assign_number_with_coeff(&to_sub.value, minus_one);
        lc.add_assign_number_with_coeff(&new_value.value, minus_one);
        lc.add_assign_boolean_with_coeff(&of, shift);

        lc.enforce_zero(cs)?;

        Ok((new_value, of))
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        condition_flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        // we do not need range checks here

        let new_value = Num::conditionally_select(cs, condition_flag, &a.value, &b.value)?;

        // for now we do not keep the bit decomposition with us
        Ok(Self {
            value: new_value,
            bits: None,
            _marker: std::marker::PhantomData,
        })
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
    ) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &a.value, &b.value)
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value.get_value()
    }

    pub fn get_value_clamped(&self) -> Option<u128> {
        self.value.get_value().map(|value| fe_to_u128(value))
    }

    pub fn get_value_as_biguint(&self) -> Option<BigUint> {
        self.value.get_value().map(|value| fe_to_biguint(&value))
    }
}

use crate::vm::primitives::small_uints::IntoFr;
use crate::vm::primitives::*;

// special case for address
impl<E: Engine> SmallFixedWidthInteger<E, U160> {
    pub fn cast_from_u160(value: crate::vm::primitives::small_uints::UInt160<E>) -> Self {
        Self {
            value: value.inner,
            bits: None,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn alloc_from_address_like<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<u160>,
    ) -> Result<Self, SynthesisError> {
        let wit = value.map(|el| <u160 as IntoFr<E>>::into_fr(el));
        Self::allocate(cs, wit)
    }

    pub fn get_value_address_like(&self) -> Option<u160> {
        let raw_value = self.get_value();
        let as_biguint = raw_value.map(|el| fe_to_biguint(&el));
        let value = as_biguint.map(|el| <u160 as From<BigUint>>::from(el));

        value
    }

    pub fn to_u160(&self) -> UInt160<E> {
        UInt160::from_num_unchecked(self.value)
    }
}

impl<E: Engine, W: WidthMarker> CSAllocatable<E> for SmallFixedWidthInteger<E, W> {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        // FIXME: Handle witness types other then u160
        Self::allocate(cs, witness)
    }
}
