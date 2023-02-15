use super::*;
use crate::glue::traits::*;
use crate::vm::primitives::{UInt16, UInt32};
use cs_derive::*;
use num_traits::Zero;
// We accumulate memory queries and then use a standard validity argument

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSEqual,
    CSSelectable,
    FixedLengthEncodableExt,
    FixedLengthDecodableExt,
)]
#[EncodingLength = "2"]
#[PackWithCS = "false"]
#[derivative(Clone, Debug)]
pub struct DelegatedMemoryWriteRecord<E: Engine> {
    pub hash: Num<E>,
    pub memory_page: UInt32<E>,
}

pub(crate) const DELEGATED_MEMORY_WRITE_RECORD_ENCODING_LEN: usize = 2;

impl<E: Engine> DelegatedMemoryWriteRecord<E> {
    pub fn pack(&self) -> [Num<E>; DELEGATED_MEMORY_WRITE_RECORD_ENCODING_LEN] {
        [self.hash, self.memory_page.inner]
    }
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSEqual,
    CSSelectable,
    FixedLengthEncodableExt,
    FixedLengthDecodableExt,
)]
#[EncodingLength = "2"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct DecommitmentRequest<E: Engine> {
    pub hash: Num<E>,
    pub memory_page: UInt32<E>,
    pub is_first: Boolean,
}

impl<E: Engine> DecommitmentRequest<E> {
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 2], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.memory_page.inner, shifts[0]);
        lc.add_assign_boolean_with_coeff(&self.is_first, shifts[32]);
        let el = lc.into_num(cs)?;

        Ok([el, self.hash])
    }
}
