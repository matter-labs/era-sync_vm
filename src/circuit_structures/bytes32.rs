use super::*;
use crate::traits::*;
use crate::vm::structural_eq::*;
use franklin_crypto::plonk::circuit::byte::{uniquely_encode_be_bytes_into_num, Byte};

use cs_derive::*;

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct Bytes32<E: Engine> {
    pub(crate) inner: [Byte<E>; 32],
}

impl<E: Engine> Copy for Bytes32<E> {}

impl<E: Engine> Bytes32<E> {
    pub const CIRCUIT_ENCODING_LEN: usize = 2;

    pub fn empty() -> Self {
        Self {
            inner: [Byte::<E>::empty(); 32],
        }
    }

    pub fn constant_from_bytes(array: &[u8; 32]) -> Self {
        let mut tmp = [Byte::<E>::zero(); 32];
        for (i, el) in array.iter().enumerate() {
            tmp[i] = Byte::<E>::constant(*el);
        }

        Self { inner: tmp }
    }

    pub fn from_bytes_array(array: &[Byte<E>; 32]) -> Self {
        Self { inner: *array }
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
        let mut result = Self {
            inner: [Byte::empty(); 32],
        };
        for ((a, b), dst) in a
            .inner
            .iter()
            .zip(b.inner.iter())
            .zip(result.inner.iter_mut())
        {
            *dst = Byte::conditionally_select(cs, condition_flag, &a, &b)?;
        }

        Ok(result)
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        use crate::vm::partitioner::smart_and;

        let mut flags = vec![];
        let shifts = compute_shifts::<E::Fr>();
        for chunk in self.inner.chunks(16) {
            let mut lc = LinearCombination::zero();
            for id in 0..16 {
                lc.add_assign_number_with_coeff(&chunk[id].inner, shifts[id * 8]);
            }
            let as_num = lc.into_num(cs)?;
            flags.push(as_num.is_zero(cs)?);
        }

        smart_and(cs, &flags)
    }

    pub fn into_u128_pair<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[UInt128<E>; 2], SynthesisError> {
        let mut res = [UInt128::zero(); 2];
        let shifts = compute_shifts::<E::Fr>();
        for (chunk_id, chunk) in self.inner.chunks(16).enumerate() {
            let mut lc = LinearCombination::zero();
            for id in 0..16 {
                lc.add_assign_number_with_coeff(&chunk[id].inner, shifts[id * 8]);
            }
            let as_num = lc.into_num(cs)?;
            res[chunk_id] = UInt128::from_num_unchecked(as_num);
        }

        Ok(res)
    }
}

impl<E: Engine> CSPackable<E, 2> for Bytes32<E> {
    fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        let [low, high] = self.into_u128_pair(cs)?;

        Ok([low.inner, high.inner])
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, 2> for Bytes32<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        self.pack(cs)
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 2> for Bytes32<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 2> for Bytes32<E> {}

impl<E: Engine> CircuitVariableLengthEncodable<E> for Bytes32<E> {
    fn encoding_length() -> usize {
        2
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let [el0, el1] = <Self as CircuitFixedLengthEncodable<E, 2>>::encode(self, cs)?;
        Ok(vec![el0, el1])
    }
}

impl<E: Engine> CircuitVariableLengthEncodableExt<E> for Bytes32<E> {}

impl<E: Engine> CircuitVariableLengthDecodableExt<E> for Bytes32<E> {
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> Bytes32Witness<E> {
    pub fn empty() -> Self {
        Self {
            inner: [0u8; 32],
            _marker: std::marker::PhantomData,
        }
    }

    pub fn from_bytes_array(array: &[u8; 32]) -> Self {
        Self {
            inner: *array,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E: Engine> Copy for Bytes32Witness<E> {}

impl<E: Engine> Default for Bytes32Witness<E> {
    fn default() -> Self {
        Self::empty()
    }
}
