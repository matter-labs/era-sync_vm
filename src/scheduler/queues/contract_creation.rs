use super::*;

use crate::vm::primitives::*;
use cs_derive::*;

// we only need to ensure that if during a transaction N contract X (newly created)
// has ended up in a ephemeral/non-ephemeral state then in VM trace of this transaction
// it has indeed passes through some chain of changes such that it ended up in the same state
// (if e.g. one reverts a parent of "create" call)

// Note on linking the address to code + creator + salt + data location: as address is uniquely
// (hash collision resistance) derived in a scheduler circuit based on code + creator + salt + data location
// then we only need to compare addresses

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSEqual,
    CSSelectable,
    FixedLengthEncodableExt,
    FixedLengthDecodableExt,
)]
#[EncodingLength = "1"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct ContractCreationRecord<E: Engine> {
    pub is_emphemeral: Boolean,
    pub tx_number_in_block: UInt16<E>,
    pub address: UInt160<E>,
}

impl<E: Engine> ContractCreationRecord<E> {
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 1], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.address.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.tx_number_in_block.inner, shifts[160]);
        lc.add_assign_boolean_with_coeff(&self.is_emphemeral, shifts[160 + 16]);
        let el = lc.into_num(cs)?;

        Ok([el])
    }
}
