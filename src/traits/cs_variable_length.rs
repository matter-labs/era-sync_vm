use super::*;
use crate::circuit_structures::utils::can_not_be_false_if_flagged;
use crate::vm::partitioner::smart_and;

pub trait CircuitVariableLengthEncodable<E: Engine>: Clone {
    fn encoding_length() -> usize;

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError>;

    fn encoding_witness(&self) -> Option<Vec<E::Fr>> {
        unimplemented!("by default it's not called by queue implementations, and is only required in very edge cases");
    }
}

impl<E: Engine> CircuitVariableLengthEncodable<E> for Num<E> {
    fn encoding_length() -> usize {
        1
    }

    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        Ok(vec![*self])
    }
}

impl<E: Engine> CircuitVariableLengthEncodable<E> for Boolean {
    fn encoding_length() -> usize {
        1
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        use franklin_crypto::plonk::circuit::linear_combination::LinearCombination;
        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&self, E::Fr::one());
        let el = lc.into_num(cs)?;

        Ok(vec![el])
    }
}

use franklin_crypto::plonk::circuit::byte::Byte;

impl<E: Engine> CircuitVariableLengthEncodable<E> for Byte<E> {
    fn encoding_length() -> usize {
        1
    }

    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        Ok(vec![self.inner])
    }
}

impl<E: Engine, T: CircuitVariableLengthEncodable<E>, const N: usize>
    CircuitVariableLengthEncodable<E> for [T; N]
{
    fn encoding_length() -> usize {
        N
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut tmp = vec![];
        for el in self.iter() {
            let packed = el.encode(cs)?;
            tmp.extend(packed);
        }

        Ok(tmp)
    }
}

pub trait CircuitVariableLengthEncodableExt<E: Engine>:
    CircuitVariableLengthEncodable<E> + CSWitnessable<E>
{
}

pub trait CircuitVariableLengthDecodableExt<E: Engine>:
    CircuitVariableLengthEncodableExt<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        unimplemented!("not implemented by default. Usually can delegate to CSAllocatable call")
    }
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            <Self as CircuitVariableLengthEncodable<E>>::encoding_length(),
            values.len()
        );
        let new = Self::allocate_from_witness(cs, witness)?;
        let encoding = <Self as CircuitVariableLengthEncodable<E>>::encode(&new, cs)?;

        for (enc, val) in encoding.iter().zip(values.iter()) {
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
        assert_eq!(
            <Self as CircuitVariableLengthEncodable<E>>::encoding_length(),
            values.len()
        );
        let new = Self::allocate_from_witness(cs, witness)?;
        let encoding = <Self as CircuitVariableLengthEncodable<E>>::encode(&new, cs)?;

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

impl<E: Engine> CircuitVariableLengthEncodable<E> for () {
    fn encoding_length() -> usize {
        0
    }

    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        Ok(vec![])
    }
}

impl<E: Engine> CircuitVariableLengthEncodableExt<E> for () {}

impl<E: Engine> CircuitVariableLengthDecodableExt<E> for () {
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Ok(())
    }
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>],
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            <Self as CircuitVariableLengthEncodable<E>>::encoding_length(),
            values.len()
        );

        Ok(())
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>],
        _should_execute: &Boolean,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            <Self as CircuitVariableLengthEncodable<E>>::encoding_length(),
            values.len()
        );

        Ok(())
    }
}

impl<E: Engine> CircuitVariableLengthEncodable<E> for std::marker::PhantomData<E> {
    fn encoding_length() -> usize {
        0
    }

    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        Ok(vec![])
    }
}

impl<E: Engine> CircuitVariableLengthEncodableExt<E> for std::marker::PhantomData<E> {}

impl<E: Engine> CircuitVariableLengthDecodableExt<E> for std::marker::PhantomData<E> {
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Ok(std::marker::PhantomData)
    }
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>],
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            <Self as CircuitVariableLengthEncodable<E>>::encoding_length(),
            values.len()
        );

        Ok(std::marker::PhantomData)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>],
        _should_execute: &Boolean,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            <Self as CircuitVariableLengthEncodable<E>>::encoding_length(),
            values.len()
        );

        Ok(std::marker::PhantomData)
    }
}
