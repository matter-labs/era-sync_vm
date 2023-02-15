use super::*;
use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;
pub use crate::traits::*;
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::rescue::PlonkCsSBox;
use franklin_crypto::rescue::*;

pub(crate) trait CircuitFixedLengthDecodable<E: Engine, const N: usize>:
    Clone + Send + Sync
{
    fn parse<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; N],
    ) -> Result<Self, SynthesisError>;
    fn parse_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; N],
        should_execute: &Boolean,
    ) -> Result<Self, SynthesisError>;
}

use crate::traits::*;

#[track_caller]
pub fn get_vec_vec_witness<E: Engine, I: CircuitFixedLengthEncodableExt<E, N>, const N: usize>(
    from: &mut Option<Vec<Vec<I::Witness>>>,
) -> Option<I::Witness> {
    if let Some(high_level_vec) = from.as_mut() {
        if let Some(last_high_level_vec) = high_level_vec.first_mut() {
            if let Some(last_inner_item) = last_high_level_vec.first().cloned() {
                let _ = last_high_level_vec.drain(0..1);
                if last_high_level_vec.is_empty() {
                    let _ = high_level_vec.drain(0..1);
                }

                Some(last_inner_item)
            } else {
                unreachable!("we can not have non-empty outer but empty inner");
            }
        } else {
            *from = None;

            Some(I::placeholder_witness())
        }
    } else {
        Some(I::placeholder_witness())
    }
}

#[track_caller]
pub fn get_vec_witness<E: Engine, I: CircuitFixedLengthEncodableExt<E, N>, const N: usize>(
    from: &mut Option<Vec<I::Witness>>,
) -> Option<I::Witness> {
    get_vec_witness_raw(from, I::placeholder_witness())
}

#[track_caller]
pub fn get_vec_witness_raw<T>(from: &mut Option<Vec<T>>, default_value_to_use: T) -> Option<T> {
    if let Some(high_level_vec) = from.as_mut() {
        if high_level_vec.first().is_some() {
            let last_inner_item = high_level_vec.drain(0..1).next().unwrap();
            if high_level_vec.is_empty() {
                // we peeked the last one
                *from = None;
            }

            Some(last_inner_item)
        } else {
            unreachable!("we can not have non-empty outer but empty inner");
        }
    } else {
        Some(default_value_to_use)
    }
}

#[track_caller]
pub fn get_vec_witness_raw_with_hint<T>(
    from: &mut Option<Vec<T>>,
    default_value_to_use: T,
) -> (Option<T>, Option<bool>) {
    if let Some(high_level_vec) = from.as_mut() {
        if high_level_vec.first().is_some() {
            let last_inner_item = high_level_vec.drain(0..1).next().unwrap();
            if high_level_vec.is_empty() {
                // we peeked the last one
                *from = None;
            }

            (Some(last_inner_item), Some(true))
        } else {
            unreachable!("we can not have non-empty outer but empty inner");
        }
    } else {
        (Some(default_value_to_use), Some(false))
    }
}

#[track_caller]
pub fn get_vec_vec_witness_raw_with_hint_on_more_in_subset<T: Clone>(
    from: &mut Option<Vec<Vec<T>>>,
    default_value_to_use: T,
) -> (Option<T>, Option<bool>) {
    if let Some(high_level_vec) = from.as_mut() {
        if let Some(last_high_level_vec) = high_level_vec.first_mut() {
            if let Some(last_inner_item) = last_high_level_vec.first().cloned() {
                let _ = last_high_level_vec.drain(0..1);
                let have_more_in_same_subset = !last_high_level_vec.is_empty();
                if last_high_level_vec.is_empty() {
                    let _ = high_level_vec.drain(0..1);
                }

                (Some(last_inner_item), Some(have_more_in_same_subset))
            } else {
                unreachable!("we can not have non-empty outer but empty inner");
            }
        } else {
            // "from" is not yet none, but compltely empty
            *from = None;

            (Some(default_value_to_use), Some(false))
        }
    } else {
        // there is nothing at all
        (Some(default_value_to_use), Some(false))
    }
}

// default implementation for Num<E>

impl<E: Engine> CircuitFixedLengthEncodable<E, 1> for Num<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        Ok([*self])
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 1]> {
        self.get_value().map(|el| [el])
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 1> for Num<E> {}

impl<E: Engine> CircuitFixedLengthDecodable<E, 1> for Num<E> {
    fn parse<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>; 1],
    ) -> Result<Self, SynthesisError> {
        Ok(values[0])
    }
    fn parse_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        should_execute: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let candidate = values[0];

        Num::conditionally_select(
            cs,
            &should_execute,
            &candidate,
            &Num::Constant(E::Fr::zero()),
        )
    }
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 1> for Num<E> {
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>; 1],
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Ok(values[0])
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        should_execute: &Boolean,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let candidate = values[0];

        Num::conditionally_select(
            cs,
            &should_execute,
            &candidate,
            &Num::Constant(E::Fr::zero()),
        )
    }
}

// default implementation for [Num<E>; N]

impl<E: Engine, const N: usize> CircuitFixedLengthEncodable<E, N> for [Num<E>; N] {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; N], SynthesisError> {
        Ok(*self)
    }

    fn encoding_witness(&self) -> Option<[E::Fr; N]> {
        Num::get_value_multiple(self)
    }
}

impl<E: Engine, const N: usize> CircuitFixedLengthEncodableExt<E, N> for [Num<E>; N] {}

impl<E: Engine, const N: usize> CircuitFixedLengthDecodable<E, N> for [Num<E>; N] {
    fn parse<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>; N],
    ) -> Result<Self, SynthesisError> {
        Ok(*values)
    }
    fn parse_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; N],
        should_execute: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let mut result = [Num::Constant(E::Fr::zero()); N];
        for (c, r) in values.iter().zip(result.iter_mut()) {
            *r = Num::conditionally_select(cs, &should_execute, &c, &*r)?;
        }

        Ok(result)
    }
}

impl<E: Engine, W: WidthMarker> CircuitFixedLengthEncodable<E, 1> for SmallFixedWidthInteger<E, W> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        Ok([self.value])
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 1]> {
        self.value.get_value().map(|el| [el])
    }
}

impl<E: Engine, W: WidthMarker> CSWitnessable<E> for SmallFixedWidthInteger<E, W> {
    type Witness = E::Fr;

    fn create_witness(&self) -> Option<Self::Witness> {
        Num::get_value_multiple(&[self.value]).map(|el| el[0])
    }
    fn placeholder_witness() -> Self::Witness {
        E::Fr::zero()
    }
}

impl<E: Engine, W: WidthMarker> CircuitFixedLengthEncodableExt<E, 1>
    for SmallFixedWidthInteger<E, W>
{
}

impl<E: Engine, W: WidthMarker> CircuitFixedLengthDecodableExt<E, 1>
    for SmallFixedWidthInteger<E, W>
{
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 1>>::encode(&new, cs)?;

        for (enc, val) in encoding.iter().zip(values.iter()) {
            enc.enforce_equal(cs, val)?;
        }

        Ok(new)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 1>>::encode(&new, cs)?;

        let mut tmp = vec![];

        for (enc, val) in encoding.iter().zip(values.iter()) {
            let eq = Num::equals(cs, &enc, val)?;
            tmp.push(eq);
        }

        let eq = smart_and(cs, &tmp)?;
        can_not_be_false_if_flagged(cs, &eq, should_execute)?;

        Ok(new)
    }
}

// default implementation for Byte<E>

impl<E: Engine> CircuitFixedLengthEncodable<E, 1> for Byte<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        Ok([self.inner])
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 1]> {
        self.inner.get_value().map(|el| [el])
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 1> for Byte<E> {}

impl<E: Engine> CircuitFixedLengthDecodable<E, 1> for Byte<E> {
    fn parse<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
    ) -> Result<Self, SynthesisError> {
        let b = values[0];
        constraint_bit_length(cs, &b, 8)?;
        let b = Byte { inner: b };

        Ok(b)
    }
    fn parse_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        should_execute: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let candidate = values[0];
        let candidate = Num::conditionally_select(
            cs,
            &should_execute,
            &candidate,
            &Num::Constant(E::Fr::zero()),
        )?;

        Self::parse(cs, &[candidate])
    }
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 1> for Byte<E> {
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let b = Byte::from_u8_witness(cs, witness)?;
        b.inner.enforce_equal(cs, &values[0])?;

        Ok(b)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        should_execute: &Boolean,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let candidate = values[0];
        let candidate = Num::conditionally_select(
            cs,
            &should_execute,
            &candidate,
            &Num::Constant(E::Fr::zero()),
        )?;

        Self::parse(cs, &[candidate])
    }
}
