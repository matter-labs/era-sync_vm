use super::*;

use crate::bellman::plonk::better_better_cs::cs::{Index, Variable};
use crate::traits::*;

// compare any two structures in a circuit to determine whether
// they are the same one in a sense that they are composed from
// the same circuit variables
pub trait CircuitEq<E: Engine> {
    fn eq(&self, other: &Self) -> bool;
}

pub trait CircuitOrd<E: Engine> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering;
}

pub trait CircuitSelectable<E: Engine>: Sized {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError>;
}

impl<E: Engine, T> CircuitEq<E> for std::marker::PhantomData<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<E: Engine, T> CircuitOrd<E> for std::marker::PhantomData<T> {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl<E: Engine, T> CircuitSelectable<E> for std::marker::PhantomData<T> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _flag: &Boolean,
        _a: &Self,
        _b: &Self,
    ) -> Result<Self, SynthesisError> {
        Ok(std::marker::PhantomData)
    }
}

impl<E: Engine, T> CircuitOrthogonalSelectable<E> for std::marker::PhantomData<T> {
    fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _reference: Self,
        _candidates: &[(Boolean, Self)],
    ) -> Result<Self, SynthesisError> {
        Ok(std::marker::PhantomData)
    }
}

impl<E: Engine, T> CSWitnessable<E> for std::marker::PhantomData<T> {
    type Witness = ();
    fn create_witness(&self) -> Option<Self::Witness> {
        Some(())
    }
    fn placeholder_witness() -> Self::Witness {
        ()
    }
}

impl<E: Engine, T> CSAllocatable<E> for std::marker::PhantomData<T> {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Ok(std::marker::PhantomData)
    }
}

impl<E: Engine, T: CircuitEq<E>> CircuitEq<E> for Option<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<E: Engine, T: CircuitOrd<E>> CircuitOrd<E> for Option<T> {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl<E: Engine, T: CircuitSelectable<E>> CircuitSelectable<E> for Option<T> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _flag: &Boolean,
        _a: &Self,
        _b: &Self,
    ) -> Result<Self, SynthesisError> {
        Ok(None)
    }
}

impl<E: Engine, T: CircuitOrthogonalSelectable<E>> CircuitOrthogonalSelectable<E> for Option<T> {
    fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _reference: Self,
        _candidates: &[(Boolean, Self)],
    ) -> Result<Self, SynthesisError> {
        Ok(None)
    }
}

impl<E: Engine> CircuitEq<E> for Variable {
    fn eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl<E: Engine> CircuitOrd<E> for Variable {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.get_unchecked(), other.get_unchecked()) {
            (Index::Input(a), Index::Input(b)) => a.cmp(&b),
            (Index::Input(_), Index::Aux(_)) => std::cmp::Ordering::Less,
            (Index::Aux(_), Index::Input(_)) => std::cmp::Ordering::Greater,
            (Index::Aux(a), Index::Aux(b)) => a.cmp(&b),
        }
    }
}

impl<E: Engine, T: CircuitEq<E>, Q: CircuitEq<E>> CircuitEq<E> for (T, Q) {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0) && self.1.eq(&other.1)
    }
}

impl<E: Engine, T: CircuitOrd<E>, Q: CircuitOrd<E>> CircuitOrd<E> for (T, Q) {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            std::cmp::Ordering::Less => return std::cmp::Ordering::Less,
            std::cmp::Ordering::Greater => return std::cmp::Ordering::Greater,
            _ => {}
        }

        match self.1.cmp(&other.1) {
            std::cmp::Ordering::Less => return std::cmp::Ordering::Less,
            std::cmp::Ordering::Greater => return std::cmp::Ordering::Greater,
            _ => {}
        }

        std::cmp::Ordering::Equal
    }
}

impl<E: Engine, T: CircuitEq<E>> CircuitEq<E> for [T] {
    fn eq(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a.eq(b))
    }
}

impl<E: Engine, T: CircuitOrd<E>> CircuitOrd<E> for [T] {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for (a, b) in self.iter().zip(other.iter()) {
            match a.cmp(&b) {
                std::cmp::Ordering::Less => return std::cmp::Ordering::Less,
                std::cmp::Ordering::Greater => return std::cmp::Ordering::Greater,
                _ => {}
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl<E: Engine, T, const N: usize> CircuitEq<E> for [T; N]
where
    T: CircuitEq<E>,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a.eq(b))
    }
}

impl<E: Engine, T, const N: usize> CircuitOrd<E> for [T; N]
where
    T: CircuitOrd<E>,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for (a, b) in self.iter().zip(other.iter()) {
            match a.cmp(&b) {
                std::cmp::Ordering::Less => return std::cmp::Ordering::Less,
                std::cmp::Ordering::Greater => return std::cmp::Ordering::Greater,
                _ => {}
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl<E: Engine, T: CircuitSelectable<E>, const N: usize> CircuitSelectable<E> for [T; N] {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut result = vec![];
        for (a, b) in a.iter().zip(b.iter()) {
            let c = T::conditionally_select(cs, flag, a, b)?;
            result.push(c);
        }
        use std::convert::TryInto;
        let result: [T; N] = result
            .try_into()
            .unwrap_or_else(|_| panic!("invalid length"));

        Ok(result)
    }
}

impl<E: Engine, T: CircuitSelectable<E>> CircuitSelectable<E> for Vec<T> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut result = vec![];
        for (a, b) in a.iter().zip(b.iter()) {
            let c = T::conditionally_select(cs, flag, a, b)?;
            result.push(c);
        }

        Ok(result)
    }
}

impl<E: Engine, T: CircuitEq<E>> CircuitEq<E> for Vec<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a.eq(b))
    }
}

impl<E: Engine, T: CircuitOrd<E>> CircuitOrd<E> for Vec<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for (a, b) in self.iter().zip(other.iter()) {
            match a.cmp(&b) {
                std::cmp::Ordering::Less => return std::cmp::Ordering::Less,
                std::cmp::Ordering::Greater => return std::cmp::Ordering::Greater,
                _ => {}
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl<E: Engine> CircuitEq<E> for AllocatedNum<E> {
    fn eq(&self, other: &Self) -> bool {
        self.get_variable() == other.get_variable()
    }
}

impl<E: Engine> CircuitOrd<E> for AllocatedNum<E> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        <Variable as CircuitOrd<E>>::cmp(&self.get_variable(), &other.get_variable())
    }
}

impl<E: Engine> CircuitSelectable<E> for AllocatedNum<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        Self::conditionally_select(cs, a, b, flag)
    }
}

impl<E: Engine> CircuitEq<E> for Num<E> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Num::Constant(a), Num::Constant(b)) => a == b,
            (Num::Variable(a), Num::Variable(b)) => <AllocatedNum<E> as CircuitEq<E>>::eq(&a, &b),
            _ => false,
        }
    }
}

impl<E: Engine> CircuitOrd<E> for Num<E> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Num::Constant(a), Num::Constant(b)) => a.into_repr().cmp(&b.into_repr()),
            (Num::Variable(a), Num::Variable(b)) => <AllocatedNum<E> as CircuitOrd<E>>::cmp(&a, &b),
            (Num::Constant(..), Num::Variable(..)) => std::cmp::Ordering::Less,
            (Num::Variable(..), Num::Constant(..)) => std::cmp::Ordering::Greater,
        }
    }
}

impl<E: Engine> CircuitSelectable<E> for Num<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        Self::conditionally_select(cs, flag, a, b)
    }
}

// impl<E: Engine> CircuitEq<E> for Term<E> {
//     fn eq(&self, other: &Self) -> bool {
//         match (self.is_constant(), other.is_constant()) {
//             (true, true) | (false, false) => {
//                 let nums_are_eq = self.num.eq(&other.num);
//                 let coeffs_are_eq = self.coeff == other.coeff;
//                 let constants_are_eq = self.constant_term == other.constant_term;

//                 nums_are_eq && coeffs_are_eq && constants_are_eq
//             },
//             _ => false
//         }
//     }
// }

// impl<E: Engine> CircuitOrd<E> for Term<E> {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         unimplemented!()
//         match (self, other) {
//             (Num::Constant(a), Num::Constant(b)) => {
//                 a.into_repr().cmp(&b.into_repr())
//             },
//             (Num::Variable(a), Num::Variable(b)) => {
//                 <AllocatedNum<E> as CircuitOrd<E>>::cmp(&a, &b)
//             },
//             (Num::Constant(..), Num::Variable(..)) => {
//                 std::cmp::Ordering::Less
//             },
//             (Num::Variable(..), Num::Constant(..)) => {
//                 std::cmp::Ordering::Greater
//             },
//         }
//     }
// }

impl<E: Engine> CircuitSelectable<E> for Term<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        Self::select(cs, flag, a, b)
    }
}

impl<E: Engine> CircuitEq<E> for Boolean {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Boolean::Constant(a), Boolean::Constant(b)) => a == b,
            (Boolean::Is(a), Boolean::Is(b)) => a.get_variable() == b.get_variable(),
            (Boolean::Not(a), Boolean::Not(b)) => a.get_variable() == b.get_variable(),
            _ => false,
        }
    }
}

impl<E: Engine> CircuitOrd<E> for Boolean {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Boolean::Constant(a), Boolean::Constant(b)) => a.cmp(&b),
            (Boolean::Constant(_a), _) => std::cmp::Ordering::Less,
            (Boolean::Is(..), Boolean::Constant(..)) => std::cmp::Ordering::Greater,
            (Boolean::Not(..), Boolean::Constant(..)) => std::cmp::Ordering::Greater,
            (Boolean::Is(..), Boolean::Not(..)) => std::cmp::Ordering::Less,
            (Boolean::Is(a), Boolean::Is(b)) => {
                <Variable as CircuitOrd<E>>::cmp(&a.get_variable(), &b.get_variable())
            }
            (Boolean::Not(..), Boolean::Is(..)) => std::cmp::Ordering::Greater,
            (Boolean::Not(a), Boolean::Not(b)) => {
                <Variable as CircuitOrd<E>>::cmp(&a.get_variable(), &b.get_variable())
            }
        }
    }
}

impl<E: Engine> CircuitSelectable<E> for Boolean {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        Self::conditionally_select(cs, flag, a, b)
    }
}

use crate::circuit_structures::SmallFixedWidthInteger;
use crate::data_structures::markers::*;

impl<E: Engine, W: WidthMarker> CircuitEq<E> for SmallFixedWidthInteger<E, W> {
    fn eq(&self, other: &Self) -> bool {
        let num_equals = self.value.eq(&other.value);
        if !num_equals {
            return false;
        }

        match (self.bits.as_ref(), other.bits.as_ref()) {
            (Some(a), Some(b)) => a
                .iter()
                .zip(b.iter())
                .all(|(a, b)| <Boolean as CircuitEq<E>>::eq(a, b)),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<E: Engine, W: WidthMarker> CircuitSelectable<E> for SmallFixedWidthInteger<E, W> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        Self::conditionally_select(cs, flag, a, b)
    }
}

impl<E: Engine> CircuitEq<E> for Byte<E> {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<E: Engine> CircuitSelectable<E> for Byte<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        Self::conditionally_select(cs, flag, a, b)
    }
}

pub trait CircuitOrthogonalSelectable<E: Engine>:
    CircuitEq<E> + CircuitOrd<E> + CircuitSelectable<E> + Clone
{
    fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        reference: Self,
        candidates: &[(Boolean, Self)],
    ) -> Result<Self, SynthesisError>;
}

// NOTE: we only implement this trait for basic types, such as Boolean, Num and arrays.
// Implementations for complex types should be derived on per-field basis

impl<E: Engine> CircuitOrthogonalSelectable<E> for Num<E> {
    fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        reference: Self,
        candidates: &[(Boolean, Self)],
    ) -> Result<Self, SynthesisError> {
        let (_, partitions) = partition(&reference, &candidates);
        let mut it = partitions.into_iter().peekable();
        let any_variants_available = it.peek().is_some();
        let mut grouped_flags = vec![];

        let mut accumulator = Num::zero();
        for (flags, value) in it {
            let flag = smart_or(cs, &flags)?;
            accumulator = value.mask_by_boolean_into_accumulator(cs, &flag, &accumulator)?;
            grouped_flags.push(flag);
        }

        let res = if any_variants_available {
            let flag = smart_or(cs, &grouped_flags)?;
            Self::conditionally_select(cs, &flag, &accumulator, &reference)?
        } else {
            reference
        };

        Ok(res)
    }
}

impl<E: Engine> CircuitOrthogonalSelectable<E> for Boolean {
    fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        reference: Self,
        candidates: &[(Boolean, Self)],
    ) -> Result<Self, SynthesisError> {
        let (_, partitions) = partition::<E, _, _>(&reference, &candidates);
        let mut it = partitions.into_iter();
        let mut new = if let Some((flags, value)) = it.next() {
            let flag = smart_or(cs, &flags)?;
            Self::conditionally_select(cs, &flag, &value, &reference)?
        } else {
            reference
        };
        for (flags, value) in it {
            let flag = smart_or(cs, &flags)?;
            new = Boolean::conditionally_select(cs, &flag, &value, &new)?;
        }

        Ok(new)
    }
}

// there are two options here:
// - either we partition by each subarray, then we expect that we usually see only small changes for array
// - or we we exepct that only small part changes

impl<E: Engine, T: CircuitOrthogonalSelectable<E>, const N: usize> CircuitOrthogonalSelectable<E>
    for [T; N]
{
    fn select_update_assuming_orthogonality<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        reference: Self,
        candidates: &[(Boolean, Self)],
    ) -> Result<Self, SynthesisError> {
        array_select_update_assuming_orthogonality_per_element_strategy(cs, reference, candidates)

        // array_select_update_assuming_orthogonality_per_full_array_strategy(
        //     cs,
        //     reference,
        //     candidates
        // )
    }
}

pub fn array_select_update_assuming_orthogonality_per_element_strategy<
    E: Engine,
    CS: ConstraintSystem<E>,
    T: CircuitOrthogonalSelectable<E>,
    const N: usize,
>(
    cs: &mut CS,
    reference: [T; N],
    candidates: &[(Boolean, [T; N])],
) -> Result<[T; N], SynthesisError> {
    use std::convert::TryInto;

    let mut result = vec![];
    for i in 0..N {
        let subset: Vec<_> = candidates
            .iter()
            .map(|el| (el.0, el.1[i].clone()))
            .collect();
        let subset_ref = reference[i].clone();
        let subresult = T::select_update_assuming_orthogonality(cs, subset_ref, &subset)?;
        result.push(subresult);
    }

    let result: [T; N] = if let Ok(res) = result.try_into() {
        res
    } else {
        unreachable!()
    };

    Ok(result)
}

pub fn array_select_update_assuming_orthogonality_per_full_array_strategy<
    E: Engine,
    CS: ConstraintSystem<E>,
    T: CircuitEq<E> + CircuitOrd<E> + CircuitSelectable<E> + Clone,
    const N: usize,
>(
    cs: &mut CS,
    reference: [T; N],
    candidates: &[(Boolean, [T; N])],
) -> Result<[T; N], SynthesisError> {
    let (_, partitions) = partition::<E, _, _>(&reference, &candidates);
    let mut it = partitions.into_iter();
    let mut new = if let Some((flags, value)) = it.next() {
        let flag = smart_or(cs, &flags)?;
        <[T; N]>::conditionally_select(cs, &flag, &value, &reference)?
    } else {
        reference
    };
    for (flags, value) in it {
        let flag = smart_or(cs, &flags)?;
        new = <[T; N]>::conditionally_select(cs, &flag, &value, &new)?;
    }

    Ok(new)
}
