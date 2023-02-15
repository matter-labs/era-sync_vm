use super::*;
use crate::vm::primitives::*;
use cs_derive::*;
use num_traits::Zero;

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
pub struct WithdrawInformationPubdata<E: Engine> {
    pub token_address: UInt160<E>,
    pub address: UInt160<E>,
    pub amount: UInt256<E>,
}

pub(crate) const WITHDRAW_PUBDATA_ENCODING_LENGTH: usize = 4;

impl<E: Engine> WithdrawInformationPubdata<E> {
    pub fn empty() -> Self {
        Self {
            token_address: UInt160::zero(),
            address: UInt160::zero(),
            amount: UInt256::zero(),
        }
    }
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; WITHDRAW_PUBDATA_ENCODING_LENGTH], SynthesisError> {
        let [low, high] = self.amount.into_u128_pair(cs)?;

        Ok([
            self.token_address.inner,
            self.address.inner,
            low.inner,
            high.inner,
        ])
    }
}
