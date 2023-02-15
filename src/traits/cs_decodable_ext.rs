use super::*;
use crate::circuit_structures::utils::can_not_be_false_if_flagged;
use crate::vm::partitioner::smart_and;

pub trait CircuitFixedLengthDecodableExt<E: Engine, const N: usize>:
    CircuitFixedLengthEncodableExt<E, N>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        unimplemented!("not implemented by default. You can easily override it if you did implement CSWitnessable")
    }
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; N],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate_from_witness(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, N>>::encode(&new, cs)?;

        for (enc, val) in encoding.iter().zip(values.iter()) {
            enc.enforce_equal(cs, val)?;
        }

        Ok(new)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; N],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate_from_witness(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, N>>::encode(&new, cs)?;

        for (enc, val) in encoding.iter().zip(values.iter()) {
            Num::conditionally_enforce_equal(cs, &should_execute, enc, val)?;
        }

        Ok(new)
    }
}
