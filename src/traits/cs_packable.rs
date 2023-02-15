use super::*;

use franklin_crypto::plonk::circuit::linear_combination::LinearCombination;

pub trait CSPackable<E: Engine, const N: usize> {
    fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; N], SynthesisError>;
}

impl<E: Engine> CSPackable<E, 1> for Num<E> {
    fn pack<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        Ok([*self])
    }
}

impl<E: Engine> CSPackable<E, 1> for Boolean {
    fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&self, E::Fr::one());
        let el = lc.into_num(cs)?;

        Ok([el])
    }
}

use franklin_crypto::plonk::circuit::byte::Byte;

impl<E: Engine> CSPackable<E, 1> for Byte<E> {
    fn pack<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        Ok([self.inner])
    }
}

// we only define for all array types, so tight packing should wrap

impl<E: Engine, T: CSPackable<E, 1>, const N: usize> CSPackable<E, N> for [T; N] {
    fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; N], SynthesisError> {
        use std::convert::TryInto;

        let mut tmp = vec![];
        for el in self.iter() {
            let packed = el.pack(cs)?;
            tmp.extend(packed);
        }
        let result: [Num<E>; N] = match tmp.try_into() {
            Ok(res) => res,
            Err(..) => unreachable!(),
        };

        Ok(result)
    }
}
