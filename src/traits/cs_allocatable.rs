use super::*;

pub trait CSAllocatable<E: Engine>: CSWitnessable<E> + Sized {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError>;
}

impl<E: Engine> CSAllocatable<E> for () {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        _witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Ok(())
    }
}

impl<E: Engine> CSAllocatable<E> for Num<E> {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Num::alloc(cs, witness)
    }
}

impl<E: Engine> CSAllocatable<E> for Boolean {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Boolean::alloc(cs, witness)
    }
}

use franklin_crypto::plonk::circuit::byte::Byte;

impl<E: Engine> CSAllocatable<E> for Byte<E> {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Byte::from_u8_witness(cs, witness)
    }
}

impl<E: Engine, T: CSAllocatable<E>, const N: usize> CSAllocatable<E> for [T; N] {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        use std::convert::TryInto;

        let mut tmp = vec![];
        for i in 0..N {
            let wit = witness.as_ref().map(|el| &el[i]).cloned();
            let el = T::alloc_from_witness(cs, wit)?;
            tmp.push(el);
        }
        let result: [T; N] = match tmp.try_into() {
            Ok(res) => res,
            Err(..) => unreachable!(),
        };

        Ok(result)
    }
}
