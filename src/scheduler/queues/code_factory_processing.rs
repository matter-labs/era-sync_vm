use super::*;
use crate::glue::traits::*;
use crate::vm::primitives::*;
use cs_derive::*;
use num_traits::Zero;
// we need to indicate for future resolution that is
// in a corresponding log queue we have after a set of transactions
// a record that some code with some salt was deployed at some address
// and then may be rolled back then we have to proocess
// that a set of factory operations ended up in a same state

#[derive(
    Derivative,
    CSWitnessable,
    CSAllocatable,
    CSEqual,
    CSSelectable,
    FixedLengthEncodableExt,
    FixedLengthDecodableExt,
)]
#[EncodingLength = "4"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct CodeFactoryRecord<E: Engine> {
    pub target_is_zkporter: Boolean,
    pub is_ephemeral: Boolean,
    pub tx_number_in_block: UInt16<E>,
    pub deployer: UInt160<E>,
    pub code_root_hash: Num<E>,
    pub salt: UInt256<E>,
    pub address: UInt160<E>,
}

impl<E: Engine> CodeFactoryRecord<E> {
    pub fn empty() -> Self {
        Self {
            target_is_zkporter: Boolean::constant(false),
            is_ephemeral: Boolean::constant(false),
            tx_number_in_block: UInt16::zero(),
            deployer: UInt160::zero(),
            code_root_hash: Num::zero(),
            salt: UInt256::zero(),
            address: UInt160::zero(),
        }
    }
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 4], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.salt.inner[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.salt.inner[1].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.salt.inner[2].inner, shifts[128]);
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.deployer.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.salt.inner[3].inner, shifts[160]);
        let el1 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.address.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.tx_number_in_block.inner, shifts[160]);
        lc.add_assign_boolean_with_coeff(&self.target_is_zkporter, shifts[160 + 16]);
        lc.add_assign_boolean_with_coeff(&self.is_ephemeral, shifts[160 + 16 + 1]);
        let el2 = lc.into_num(cs)?;

        Ok([el0, el1, el2, self.code_root_hash])
    }
}
