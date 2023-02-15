use super::*;
use crate::traits::*;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};
use std::fmt;

//custom u160 type to represent etherium address
#[allow(non_camel_case_types)]
#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct u160 {
    pub limb0: u64,
    pub limb1: u64,
    pub limb2: u32,
}

impl Into<BigUint> for u160 {
    fn into(self) -> BigUint {
        let mut res = BigUint::from(self.limb2 as u64) << 64;
        res += self.limb1;
        res <<= 64;
        res += self.limb0;
        res
    }
}

impl From<BigUint> for u160 {
    fn from(el: BigUint) -> Self {
        let mask = BigUint::from(1u64) << 64;
        let (el, l0) = el.div_rem(&mask);
        let (el, l1) = el.div_rem(&mask);
        let (el, l2) = el.div_rem(&mask);
        assert!(el.is_zero());
        Self {
            limb0: l0.to_u64().unwrap(),
            limb1: l1.to_u64().unwrap(),
            limb2: l2.to_u32().unwrap(),
        }
    }
}

impl fmt::Display for u160 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:X}{:X}{:X}", self.limb2, self.limb1, self.limb0)
    }
}

impl u160 {
    pub fn zero() -> Self {
        Self::from_u64(0)
    }

    pub const fn from_u64(val: u64) -> Self {
        u160 {
            limb0: val,
            limb1: 0,
            limb2: 0,
        }
    }

    pub fn into_biguint(self) -> BigUint {
        let mut result = BigUint::from(self.limb2 as u64);
        result <<= 64;
        result += BigUint::from(self.limb1);
        result <<= 64;
        result += BigUint::from(self.limb0);

        result
    }

    pub fn from_fields_options(
        val0: Option<u64>,
        val1: Option<u64>,
        val2: Option<u64>,
    ) -> Option<Self> {
        if [val0, val1, val2].iter().any(|x| x.is_none()) {
            None
        } else {
            let res = u160 {
                limb0: val0.unwrap(),
                limb1: val1.unwrap(),
                limb2: val2.unwrap() as u32,
            };
            Some(res)
        }
    }

    pub fn to_bytes_be(&self) -> [u8; 20] {
        let mut result = [0u8; 20];
        result[12..20].copy_from_slice(&self.limb0.to_be_bytes());
        result[4..12].copy_from_slice(&self.limb1.to_be_bytes());
        result[0..4].copy_from_slice(&self.limb2.to_be_bytes());

        result
    }
}

pub trait IntoFr<E: Engine> {
    fn into_fr(self) -> E::Fr;
}

impl<E: Engine> IntoFr<E> for bool {
    fn into_fr(self) -> E::Fr {
        u64_to_fe(self as u64)
    }
}

impl<E: Engine> IntoFr<E> for u8 {
    fn into_fr(self) -> E::Fr {
        u64_to_fe(self as u64)
    }
}

impl<E: Engine> IntoFr<E> for u16 {
    fn into_fr(self) -> E::Fr {
        u64_to_fe(self as u64)
    }
}

impl<E: Engine> IntoFr<E> for u32 {
    fn into_fr(self) -> E::Fr {
        u64_to_fe(self as u64)
    }
}

impl<E: Engine> IntoFr<E> for u64 {
    fn into_fr(self) -> E::Fr {
        u64_to_fe(self)
    }
}

impl<E: Engine> IntoFr<E> for u128 {
    fn into_fr(self) -> E::Fr {
        u128_to_fe(self)
    }
}

impl<E: Engine> IntoFr<E> for u160 {
    fn into_fr(self) -> E::Fr {
        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.as_mut()[0] = self.limb0;
        repr.as_mut()[1] = self.limb1;
        repr.as_mut()[2] = self.limb2 as u64;
        <E::Fr>::from_repr(repr).unwrap()
    }
}

macro_rules! construct_uint_gadget_basic {
    ([$struct_name:ident, $base_type:ty, $width:expr]) => {
        #[derive(Derivative)]
        #[derivative(Clone, Debug)]
        pub struct $struct_name<E: Engine> {
            pub inner: Num<E>,
        }

        impl<E: Engine> Copy for $struct_name<E> {}

        impl<E: Engine> CircuitEq<E> for $struct_name<E> {
            fn eq(&self, other: &Self) -> bool {
                self.inner.eq(&other.inner)
            }
        }

        impl<E: Engine> CircuitOrd<E> for $struct_name<E> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.inner.cmp(&other.inner)
            }
        }

        impl<E: Engine> CircuitSelectable<E> for $struct_name<E> {
            fn conditionally_select<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                flag: &Boolean,
                a: &Self,
                b: &Self,
            ) -> Result<Self, SynthesisError> {
                if CircuitEq::eq(&a.inner, &b.inner) {
                    return Ok(*a);
                }
                let inner = Num::conditionally_select(cs, flag, &a.inner, &b.inner)?;
                Ok(Self::from_num_unchecked(inner))
            }
        }

        impl<E: Engine> CircuitOrthogonalSelectable<E> for $struct_name<E> {
            fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                reference: Self,
                candidates: &[(Boolean, Self)],
            ) -> Result<Self, SynthesisError> {
                let ref_num = reference.inner;
                let candidates: Vec<_> = candidates.iter().map(|el| (el.0, el.1.inner)).collect();
                let inner = Num::select_update_assuming_orthogonality(cs, ref_num, &candidates)?;
                Ok(Self::from_num_unchecked(inner))
            }
        }

        impl<E: Engine> Default for $struct_name<E> {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl<E: Engine> IntoBytes<E> for $struct_name<E> {
            fn into_le_bytes<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<Vec<Byte<E>>, SynthesisError> {
                let num_bytes = $width / 8;

                let result = match self.inner {
                    Num::Variable(ref var) => {
                        if cs
                            .get_table(crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME)
                            .is_ok()
                        {
                            let chunks =
                                constraint_bit_length_assuming_8x8_table(cs, &self.inner, $width)?;
                            let as_bytes = chunks
                                .into_iter()
                                .map(|el| Byte::from_num_unconstrained(cs, el))
                                .collect();

                            return Ok(as_bytes);
                        }
                        let mut minus_one = E::Fr::one();
                        minus_one.negate();
                        let factor = E::Fr::from_str("256").unwrap();
                        let mut coeff = E::Fr::one();
                        let mut result = Vec::with_capacity(num_bytes);
                        let mut lc = LinearCombination::zero();
                        lc.add_assign_number_with_coeff(&self.inner, minus_one);
                        let witness = split_some_into_slices(var.get_value(), 8, num_bytes);
                        for w in witness.into_iter() {
                            let allocated = AllocatedNum::alloc(cs, || Ok(*w.get()?))?;
                            let num = Num::Variable(allocated);
                            let byte = Byte::from_num(cs, num.clone())?;
                            result.push(byte);

                            lc.add_assign_number_with_coeff(&num, coeff);
                            coeff.mul_assign(&factor);
                        }

                        lc.enforce_zero(cs)?;
                        result
                    }
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

            fn into_be_bytes<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<Vec<Byte<E>>, SynthesisError> {
                let mut tmp = self.into_le_bytes(cs)?;
                tmp.reverse();

                Ok(tmp)
            }
        }

        impl<E: Engine> $struct_name<E> {
            pub fn zero() -> Self {
                Self {
                    inner: Num::Constant(E::Fr::zero()),
                }
            }

            pub fn from_num_unchecked(num: Num<E>) -> Self {
                Self { inner: num }
            }

            pub fn from_num_checked<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                value: &Num<E>,
            ) -> Result<Self, SynthesisError> {
                if !value.is_constant() {
                    constraint_bit_length(cs, &value, Self::WIDTH)?;
                } else {
                    let value = value.get_constant_value();
                    let width = value.into_repr().num_bits() as usize;
                    if width > Self::WIDTH {
                        panic!("Constant is too large: {} for {} bits", value, Self::WIDTH);
                    }
                }
                let new = Self {
                    inner: value.clone(),
                };

                Ok(new)
            }

            pub fn from_uint(x: $base_type) -> Self {
                Self {
                    inner: Num::Constant(<$base_type as IntoFr<E>>::into_fr(x)),
                }
            }

            pub const WIDTH: usize = $width;

            pub fn constant(value: E::Fr) -> Self {
                let width = value.into_repr().num_bits() as usize;
                assert!(width <= Self::WIDTH);

                let value = Num::Constant(value);
                let new = Self { inner: value };

                new
            }

            #[track_caller]
            pub fn allocate<CS>(
                cs: &mut CS,
                value: Option<$base_type>,
            ) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let value = value.map(|el| <$base_type as IntoFr<E>>::into_fr(el));
                let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
                let value = Num::Variable(allocated);
                constraint_bit_length(cs, &value, Self::WIDTH)?;

                let new = Self { inner: value };

                Ok(new)
            }

            #[track_caller]
            pub fn alloc_and_return_u8_chunks<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                value: Option<$base_type>,
            ) -> Result<(Self, [Num<E>; $width / 8]), SynthesisError> {
                let fe = value.map(|el| <$base_type as IntoFr<E>>::into_fr(el));
                let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
                let subchunks = constraint_bit_length_assuming_8x8_table(cs, &allocated, $width)?;
                let chunks: [_; $width / 8] = subchunks.try_into().unwrap();
                let new = Self::from_num_unchecked(allocated);

                Ok((new, chunks))
            }

            pub fn allocate_from_fe<CS>(
                cs: &mut CS,
                value: Option<E::Fr>,
            ) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
                let value = Num::Variable(allocated);
                constraint_bit_length(cs, &value, Self::WIDTH)?;

                let new = Self { inner: value };

                Ok(new)
            }

            pub fn allocate_unchecked<CS>(
                cs: &mut CS,
                value: Option<$base_type>,
            ) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let value = value.map(|el| <$base_type as IntoFr<E>>::into_fr(el));
                let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
                let value = Num::Variable(allocated);
                let new = Self { inner: value };

                Ok(new)
            }

            pub fn allocate_in_optimization_context_with_applicability<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                value: Option<$base_type>,
                ctx: &mut OptimizationContext<E>,
                applies: Boolean,
                marker: CtxMarker,
            ) -> Result<Self, SynthesisError> {
                let value = value.map(|el| <$base_type as IntoFr<E>>::into_fr(el));
                let allocated = AllocatedNum::alloc(cs, || Ok(*value.get()?))?;
                let value = Num::Variable(allocated);
                ctx.add_range_check(cs, &value, applies, marker, Self::WIDTH)?;

                let new = Self { inner: value };

                Ok(new)
            }

            pub fn into_num(&self) -> Num<E> {
                self.inner.clone()
            }

            pub fn decompose_into_uint32_in_place<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<[UInt32<E>; $width / 32], SynthesisError> {
                let is_constant = self.inner.is_constant();
                let witness_chunks =
                    split_some_into_slices(self.inner.get_value(), 32, $width / 32);

                let mut res = [UInt32::zero(); $width / 32];
                for (out, wit) in res.iter_mut().zip(witness_chunks.iter()) {
                    let tmp = if is_constant {
                        UInt32::constant(wit.unwrap())
                    } else {
                        UInt32::allocate_from_fe(cs, wit.clone())?
                    };
                    *out = tmp;
                }

                let shifts = compute_shifts();
                let mut offset = 0;
                let mut lc = LinearCombination::zero();
                for chunk in res.iter() {
                    lc.add_assign_number_with_coeff(&chunk.inner, shifts[offset]);
                    offset += 32;
                }
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                lc.add_assign_number_with_coeff(&self.inner, minus_one);
                lc.enforce_zero(cs)?;

                Ok(res)
            }

            pub fn decompose_into_uint16_in_place<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<[UInt16<E>; $width / 16], SynthesisError> {
                let is_constant = self.inner.is_constant();
                let witness_chunks =
                    split_some_into_slices(self.inner.get_value(), 16, $width / 16);

                let mut res = [UInt16::zero(); $width / 16];
                for (out, wit) in res.iter_mut().zip(witness_chunks.iter()) {
                    let tmp = if is_constant {
                        UInt16::constant(wit.unwrap())
                    } else {
                        UInt16::allocate_from_fe(cs, wit.clone())?
                    };
                    *out = tmp;
                }

                let shifts = compute_shifts();
                let mut offset = 0;
                let mut lc = LinearCombination::zero();
                for chunk in res.iter() {
                    lc.add_assign_number_with_coeff(&chunk.inner, shifts[offset]);
                    offset += 16;
                }
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                lc.add_assign_number_with_coeff(&self.inner, minus_one);
                lc.enforce_zero(cs)?;

                Ok(res)
            }

            pub fn decompose_into_uint8_in_place<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<[UInt8<E>; $width / 8], SynthesisError> {
                let is_constant = self.inner.is_constant();
                let witness_chunks = split_some_into_slices(self.inner.get_value(), 8, $width / 8);

                let mut res = [UInt8::zero(); $width / 8];
                for (out, wit) in res.iter_mut().zip(witness_chunks.iter()) {
                    let tmp = if is_constant {
                        UInt8::constant(wit.unwrap())
                    } else {
                        UInt8::allocate_from_fe(cs, wit.clone())?
                    };
                    *out = tmp;
                }

                let shifts = compute_shifts();
                let mut offset = 0;
                let mut lc = LinearCombination::zero();
                for chunk in res.iter() {
                    lc.add_assign_number_with_coeff(&chunk.inner, shifts[offset]);
                    offset += 8;
                }
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                lc.add_assign_number_with_coeff(&self.inner, minus_one);
                lc.enforce_zero(cs)?;

                Ok(res)
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
                let new_value = Num::conditionally_select(cs, condition_flag, &a.inner, &b.inner)?;

                Ok(Self { inner: new_value })
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
                let (left, right) =
                    Num::conditionally_reverse(cs, &a.inner, &b.inner, &condition_flag)?;

                Ok((
                    Self::from_num_unchecked(left),
                    Self::from_num_unchecked(right),
                ))
            }

            pub fn from_boolean<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                value: &Boolean,
            ) -> Result<Self, SynthesisError> {
                let num = Term::from_boolean(&value).collapse_into_num(cs)?;
                Ok(Self { inner: num })
            }

            /// Returns 0 if mask is not set
            pub fn mask<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                mask: &Boolean,
            ) -> Result<Self, SynthesisError> {
                let inner = Num::mask(cs, &self.inner, mask)?;

                Ok(Self { inner })
            }

            pub fn is_zero<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<Boolean, SynthesisError> {
                self.inner.is_zero(cs)
            }

            pub fn equals<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                a: &Self,
                b: &Self,
            ) -> Result<Boolean, SynthesisError> {
                Num::equals(cs, &a.inner, &b.inner)
            }

            pub fn conditionally_replace<CS: ConstraintSystem<E>>(
                &mut self,
                cs: &mut CS,
                condition: &Boolean,
                new_value: &Self,
            ) -> Result<(), SynthesisError> {
                *self = Self::conditionally_select(cs, condition, new_value, &self)?;
                Ok(())
            }
        }

        impl<E: Engine> CSWitnessable<E> for $struct_name<E> {
            type Witness = $base_type;
            fn create_witness(&self) -> Option<Self::Witness> {
                self.get_value()
            }
            fn placeholder_witness() -> Self::Witness {
                <$base_type>::zero()
            }
        }

        impl<E: Engine> CSAllocatable<E> for $struct_name<E> {
            fn alloc_from_witness<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                witness: Option<Self::Witness>,
            ) -> Result<Self, SynthesisError> {
                Self::allocate(cs, witness)
            }
        }

        impl<E: Engine> $struct_name<E> {
            pub const CIRCUIT_ENCODING_LEN: usize = 1;
        }

        impl<E: Engine> CSPackable<E, 1> for $struct_name<E> {
            fn pack<CS: ConstraintSystem<E>>(
                &self,
                _cs: &mut CS,
            ) -> Result<[Num<E>; 1], SynthesisError> {
                Ok([self.inner])
            }
        }

        impl<E: Engine> CircuitFixedLengthEncodable<E, 1> for $struct_name<E> {
            fn encode<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<[Num<E>; 1], SynthesisError> {
                self.pack(cs)
            }
        }

        impl<E: Engine> CircuitFixedLengthEncodableExt<E, 1> for $struct_name<E> {}

        impl<E: Engine> CircuitFixedLengthDecodableExt<E, 1> for $struct_name<E> {
            fn allocate_from_witness<CS: ConstraintSystem<E>>(
                cs: &mut CS,
                witness: Option<Self::Witness>,
            ) -> Result<Self, SynthesisError> {
                <Self as CSAllocatable<E>>::alloc_from_witness(cs, witness)
            }
        }

        impl<E: Engine> CircuitVariableLengthEncodable<E> for $struct_name<E> {
            fn encoding_length() -> usize {
                1
            }

            fn encode<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<Vec<Num<E>>, SynthesisError> {
                let mut result = vec![];
                result.extend(self.pack(cs)?);

                Ok(result)
            }
        }

        impl<E: Engine> CircuitEmpty<E> for $struct_name<E> {
            fn empty() -> Self {
                Self::zero()
            }
        }
    };
}

macro_rules! construct_uint_gadget_arithmetic {
    ([$struct_name:ident, $base_type:ty, $width:expr]) => {
        impl<E: Engine> $struct_name<E> {
            #[track_caller]
            pub fn get_value(&self) -> Option<$base_type> {
                self.inner.get_value().map(|el| {
                    let repr = el.into_repr();
                    for &limb in repr.as_ref()[2..].iter() {
                        assert_eq!(limb, 0);
                    }
                    let mut val: u128 = repr.as_ref()[1] as u128;
                    val <<= 64;
                    val += repr.as_ref()[0] as u128;
                    assert!(val <= <$base_type>::max_value() as u128);

                    val as $base_type
                })
            }

            pub fn conditionally_increment_unchecked<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                condition: &Boolean,
            ) -> Result<Self, SynthesisError> {
                let one = Num::Constant(E::Fr::one());
                let res = one.mask_by_boolean_into_accumulator(cs, &condition, &self.inner)?;
                Ok(Self { inner: res })
            }

            pub fn conditionally_decrement_unchecked<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                condition: &Boolean,
            ) -> Result<Self, SynthesisError> {
                let mut minus_one_fr = E::Fr::one();
                minus_one_fr.negate();

                let minus_one = Num::Constant(minus_one_fr);
                let res =
                    minus_one.mask_by_boolean_into_accumulator(cs, &condition, &self.inner)?;
                Ok(Self { inner: res })
            }

            pub fn conditionally_increment_checked<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                condition: &Boolean,
            ) -> Result<(Self, Boolean), SynthesisError> {
                let one = Num::Constant(E::Fr::one());
                let full = one.mask_by_boolean_into_accumulator(cs, &condition, &self.inner)?;

                let (value_witness, of_witness) = match (self.get_value(), condition.get_value()) {
                    (Some(current), Some(condition)) => {
                        let (res, of) = current.overflowing_add(condition as $base_type);
                        (Some(res), Some(of))
                    }
                    _ => (None, None),
                };

                let result = Self::allocate(cs, value_witness)?;
                let new_of = Boolean::from(AllocatedBit::alloc(cs, of_witness)?);

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut shift = E::Fr::one();
                for _ in 0..Self::WIDTH {
                    shift.double();
                }

                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&result.inner, E::Fr::one());
                lc.add_assign_boolean_with_coeff(&new_of, shift);
                lc.add_assign_number_with_coeff(&full, minus_one);
                lc.enforce_zero(cs)?;

                Ok((result, new_of))
            }

            pub fn add<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                other: &Self,
            ) -> Result<(Self, Boolean), SynthesisError> {
                let (value_witness, of_witness) = match (self.get_value(), other.get_value()) {
                    (Some(current), Some(other)) => {
                        let (res, of) = current.overflowing_add(other);

                        (Some(res), Some(of))
                    }
                    _ => (None, None),
                };

                let result = Self::allocate(cs, value_witness)?;

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
                lc.add_assign_number_with_coeff(&other.inner, E::Fr::one());
                lc.add_assign_boolean_with_coeff(&new_of, shift);
                lc.add_assign_number_with_coeff(&result.inner, minus_one);

                lc.enforce_zero(cs)?;

                Ok((result, new_of))
            }

            pub fn add_using_delayed_bool_allocation<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                other: &Self,
                optimizer: &mut OptimizationContext<E>,
            ) -> Result<(Self, Boolean), SynthesisError> {
                let (value_witness, of_witness) = match (self.get_value(), other.get_value()) {
                    (Some(current), Some(other)) => {
                        let (res, of) = current.overflowing_add(other);

                        (Some(res), Some(of))
                    }
                    _ => (None, None),
                };

                let result = Self::allocate(cs, value_witness)?;

                let new_of = optimizer.allocate_boolean(cs, of_witness)?;

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut shift = E::Fr::one();
                for _ in 0..Self::WIDTH {
                    shift.double();
                }
                shift.negate();

                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self.inner, E::Fr::one());
                lc.add_assign_number_with_coeff(&other.inner, E::Fr::one());
                lc.add_assign_boolean_with_coeff(&new_of, shift);
                lc.add_assign_number_with_coeff(&result.inner, minus_one);

                lc.enforce_zero(cs)?;

                Ok((result, new_of))
            }

            pub fn sub<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                other: &Self,
            ) -> Result<(Self, Boolean), SynthesisError> {
                let (value_witness, of_witness) = match (self.get_value(), other.get_value()) {
                    (Some(current), Some(other)) => {
                        let (res, of) = current.overflowing_sub(other);

                        (Some(res), Some(of))
                    }
                    _ => (None, None),
                };

                let result = Self::allocate(cs, value_witness)?;

                let new_of = Boolean::from(AllocatedBit::alloc(cs, of_witness)?);

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut shift = E::Fr::one();
                for _ in 0..Self::WIDTH {
                    shift.double();
                }

                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self.inner, E::Fr::one());
                lc.add_assign_number_with_coeff(&other.inner, minus_one);
                lc.add_assign_boolean_with_coeff(&new_of, shift);
                lc.add_assign_number_with_coeff(&result.inner, minus_one);

                lc.enforce_zero(cs)?;

                Ok((result, new_of))
            }

            pub fn sub_no_underflow<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                other: &Self,
            ) -> Result<Self, SynthesisError> {
                let value_witness = match (self.get_value(), other.get_value()) {
                    (Some(current), Some(other)) => {
                        let (res, of) = current.overflowing_sub(other);
                        assert!(!of);

                        Some(res)
                    }
                    _ => None,
                };

                let result = Self::allocate(cs, value_witness)?;

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self.inner, E::Fr::one());
                lc.add_assign_number_with_coeff(&other.inner, minus_one);
                lc.add_assign_number_with_coeff(&result.inner, minus_one);

                lc.enforce_zero(cs)?;

                Ok(result)
            }

            pub fn sub_using_delayed_bool_allocation<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                other: &Self,
                optimizer: &mut OptimizationContext<E>,
            ) -> Result<(Self, Boolean), SynthesisError> {
                let (value_witness, of_witness) = match (self.get_value(), other.get_value()) {
                    (Some(current), Some(other)) => {
                        let (res, of) = current.overflowing_sub(other);

                        (Some(res), Some(of))
                    }
                    _ => (None, None),
                };

                let result = Self::allocate(cs, value_witness)?;

                let new_of = optimizer.allocate_boolean(cs, of_witness)?;

                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut shift = E::Fr::one();
                for _ in 0..Self::WIDTH {
                    shift.double();
                }

                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self.inner, E::Fr::one());
                lc.add_assign_number_with_coeff(&other.inner, minus_one);
                lc.add_assign_boolean_with_coeff(&new_of, shift);
                lc.add_assign_number_with_coeff(&result.inner, minus_one);

                lc.enforce_zero(cs)?;

                Ok((result, new_of))
            }

            /// Performs speculative addition with forbidden overflow of the intermediate result
            /// even if we do nothing at the end
            #[track_caller]
            pub fn speculative_add<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
                to_add: &Self,
                execute: &Boolean,
            ) -> Result<Self, SynthesisError> {
                let new_result_witness_value =
                    match (self.get_value(), to_add.get_value(), execute.get_value()) {
                        (Some(current), Some(to_add), Some(execute)) => {
                            let mut new = current;
                            if execute {
                                new += to_add;
                            }

                            Some(new)
                        }
                        _ => None,
                    };

                // this will contain a range check
                let new_value = Self::allocate(cs, new_result_witness_value)?;

                let as_num_result = self.inner.add(cs, &to_add.into_num())?;
                let result_is_correct = Num::equals(cs, &as_num_result, &new_value.inner)?;

                can_not_be_false_if_flagged(cs, &result_is_correct, &execute)?;

                // select new or old value
                let new_value = Self::conditionally_select(cs, execute, &new_value, &self)?;

                Ok(new_value)
            }

            /// Performs speculative subtraction with forbidden overflow of the intermediate result
            /// even if we do nothing at the end
            #[track_caller]
            pub fn speculative_sub<CS>(
                &self,
                cs: &mut CS,
                to_sub: &Self,
                execute: &Boolean,
            ) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let new_result_witness_value =
                    match (self.get_value(), to_sub.get_value(), execute.get_value()) {
                        (Some(current), Some(to_sub), Some(execute)) => {
                            let mut new = current;
                            if execute {
                                new = new.wrapping_sub(to_sub);
                                // new -= to_sub;
                            }

                            Some(new)
                        }
                        _ => None,
                    };

                // this will contait a range check
                let new_value = Self::allocate(cs, new_result_witness_value)?;

                let as_num_result = self.inner.sub(cs, &to_sub.into_num())?;
                let result_is_correct = Num::equals(cs, &as_num_result, &new_value.inner)?;

                can_not_be_false_if_flagged(cs, &result_is_correct, &execute)?;

                // select new or old value
                let new_value = Self::conditionally_select(cs, execute, &new_value, &self)?;

                Ok(new_value)
            }

            pub fn increment_unchecked<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let mut el = LinearCombination::zero();
                el.add_assign_number_with_coeff(&self.inner, E::Fr::one());
                el.add_assign_constant(E::Fr::one());
                let el = el.into_num(cs)?;

                Ok(Self::from_num_unchecked(el))
            }

            pub fn add_unchecked<CS>(
                &self,
                cs: &mut CS,
                other: &Self,
            ) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let mut el = LinearCombination::zero();
                el.add_assign_number_with_coeff(&self.inner, E::Fr::one());
                el.add_assign_number_with_coeff(&other.inner, E::Fr::one());
                let el = el.into_num(cs)?;

                Ok(Self::from_num_unchecked(el))
            }

            pub fn increment_checked<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<(Self, Boolean), SynthesisError> {
                let other = Self::from_num_unchecked(Num::Constant(E::Fr::one()));
                self.add(cs, &other)
            }

            pub fn decrement_checked<CS: ConstraintSystem<E>>(
                &self,
                cs: &mut CS,
            ) -> Result<(Self, Boolean), SynthesisError> {
                let other = Self::from_num_unchecked(Num::Constant(E::Fr::one()));
                self.sub(cs, &other)
            }

            pub fn decrement_unchecked<CS>(&self, cs: &mut CS) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut el = LinearCombination::zero();
                el.add_assign_number_with_coeff(&self.inner, E::Fr::one());
                el.add_assign_constant(minus_one);
                let el = el.into_num(cs)?;

                Ok(Self::from_num_unchecked(el))
            }

            pub fn from_bytes_le<CS>(
                cs: &mut CS,
                bytes: &[Byte<E>; $width / 8],
            ) -> Result<Self, SynthesisError>
            where
                CS: ConstraintSystem<E>,
            {
                let byte_shift = u64_to_fe::<E::Fr>(256u64);
                let mut shift = E::Fr::one();
                let mut lc = LinearCombination::zero();
                for byte in bytes.iter() {
                    lc.add_assign_number_with_coeff(&byte.inner, shift);
                    shift.mul_assign(&byte_shift);
                }
                let el = lc.into_num(cs)?;

                Ok(Self::from_num_unchecked(el))
            }
        }
    };
}

macro_rules! construct_uint_gadget {
    ([$struct_name:ident, $base_type:ty, $width:expr]) => {
        construct_uint_gadget_basic!([$struct_name, $base_type, $width]);
    };
    ([$struct_name:ident, $base_type:ty, $width:expr, $_with_arithmetic: expr]) => {
        construct_uint_gadget_basic!([$struct_name, $base_type, $width]);
        construct_uint_gadget_arithmetic!([$struct_name, $base_type, $width]);
    };
}
const ARITHMETIC_FRIENDLY_UINT_TYPE: bool = true;

construct_uint_gadget!([UInt8, u8, 8, ARITHMETIC_FRIENDLY_UINT_TYPE]);
construct_uint_gadget!([UInt16, u16, 16, ARITHMETIC_FRIENDLY_UINT_TYPE]);
construct_uint_gadget!([UInt32, u32, 32, ARITHMETIC_FRIENDLY_UINT_TYPE]);
construct_uint_gadget!([UInt64, u64, 64, ARITHMETIC_FRIENDLY_UINT_TYPE]);
construct_uint_gadget!([UInt128, u128, 128, ARITHMETIC_FRIENDLY_UINT_TYPE]);
construct_uint_gadget!([UInt160, u160, 160]);

impl<E: Engine> UInt160<E> {
    #[track_caller]
    pub fn get_value(&self) -> Option<u160> {
        self.inner.get_value().map(|el| {
            let repr = el.into_repr();
            for &limb in repr.as_ref()[3..].iter() {
                assert_eq!(limb, 0);
            }
            assert!(repr.as_ref()[2] < (1u64 << 32));

            u160 {
                limb0: repr.as_ref()[0],
                limb1: repr.as_ref()[1],
                limb2: repr.as_ref()[2] as u32,
            }
        })
    }

    pub fn sub_using_delayed_bool_allocation<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
        optimizer: &mut OptimizationContext<E>,
    ) -> Result<(Self, Boolean), SynthesisError> {
        let (value_witness, of_witness) = match (self.get_value(), other.get_value()) {
            (Some(current), Some(other)) => {
                let current = current.into_biguint();
                let other = other.into_biguint();
                let of = &current < &other;
                let extra = BigUint::from(of as u64) << Self::WIDTH;
                let res = current + extra - other;

                let res = u160::from(res);

                (Some(res), Some(of))
            }
            _ => (None, None),
        };

        let result = Self::allocate(cs, value_witness)?;

        let new_of = optimizer.allocate_boolean(cs, of_witness)?;

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut shift = E::Fr::one();
        for _ in 0..Self::WIDTH {
            shift.double();
        }

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&other.inner, minus_one);
        lc.add_assign_boolean_with_coeff(&new_of, shift);
        lc.add_assign_number_with_coeff(&result.inner, minus_one);

        lc.enforce_zero(cs)?;

        Ok((result, new_of))
    }

    pub fn into_uint256_unchecked<CS>(&self, cs: &mut CS) -> Result<UInt256<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let res = if self.inner.is_constant() {
            let value = self.get_value().unwrap();

            let chunk0 = UInt64::from_num_unchecked(Num::Constant(u64_to_fe(value.limb0)));
            let chunk1 = UInt64::from_num_unchecked(Num::Constant(u64_to_fe(value.limb1)));
            let chunk2 = UInt64::from_num_unchecked(Num::Constant(u64_to_fe(value.limb2 as u64)));

            UInt256 {
                inner: [chunk0, chunk1, chunk2, UInt64::zero()],
            }
        } else {
            let value = self.get_value();

            let chunk0 =
                UInt64::from_num_unchecked(Num::Variable(AllocatedNum::alloc(cs, || {
                    let value = value.grab()?;
                    Ok(u64_to_fe(value.limb0))
                })?));

            let chunk1 =
                UInt64::from_num_unchecked(Num::Variable(AllocatedNum::alloc(cs, || {
                    let value = value.grab()?;
                    Ok(u64_to_fe(value.limb1))
                })?));

            let chunk2 =
                UInt64::from_num_unchecked(Num::Variable(AllocatedNum::alloc(cs, || {
                    let value = value.grab()?;
                    Ok(u64_to_fe(value.limb2 as u64))
                })?));

            UInt256 {
                inner: [chunk0, chunk1, chunk2, UInt64::zero()],
            }
        };

        Ok(res)
    }
}

impl<E: Engine> UInt32<E> {
    pub fn div_rem<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(Self, Self), SynthesisError> {
        let (q_witness, rem_witness) = match (self.get_value(), other.get_value()) {
            (Some(current), Some(other)) => {
                let (q, r) = current.div_rem(&other);

                (Some(q), Some(r))
            }
            _ => (None, None),
        };

        let _ = other.inner.inverse(cs)?;

        let q = Self::allocate(cs, q_witness)?;

        let r = Self::allocate(cs, rem_witness)?;

        let (_, uf) = r.sub(cs, other)?;
        Boolean::enforce_equal(cs, &uf, &Boolean::constant(true))?;

        let mul_result = q.inner.mul(cs, &other.inner)?;

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&mul_result, E::Fr::one());
        lc.add_assign_number_with_coeff(&r.inner, E::Fr::one());
        lc.add_assign_number_with_coeff(&self.inner, minus_one);
        lc.enforce_zero(cs)?;

        Ok((q, r))
    }
}
