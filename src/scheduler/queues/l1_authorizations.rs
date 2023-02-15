use super::*;
use cs_derive::*;

use crate::vm::primitives::*;

// #[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, CSPackable, CSEncodable, CSDecodable)]
// #[EncodingLength = "3"]
// #[PackWithCS = "true"]
#[derive(
    Derivative,
    CSWitnessable,
    CSAllocatable,
    CSEqual,
    CSSelectable,
    CSPackable,
    CSEncodable,
    CSDecodable,
)]
#[derivative(Clone, Debug)]
pub struct L1AuthorizationPubdata<E: Engine> {
    pub address: UInt160<E>,
    pub message_hash: Bytes32<E>,
}

pub(crate) const L1_AUTHORIZATION_PUBDATA_ENCODING_LEN: usize = 3;

impl<E: Engine> L1AuthorizationPubdata<E> {
    pub fn empty() -> Self {
        Self {
            address: UInt160::zero(),
            message_hash: Bytes32::empty(),
        }
    }
    // pub fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; L1_AUTHORIZATION_PUBDATA_ENCODING_LEN], SynthesisError> {
    //     let hash_encoding = self.message_hash.pack(cs)?;

    //     Ok([self.address.inner, hash_encoding[0], hash_encoding[1]])
    // }
}

pub const L1_AUTH_DATA_ENCODING_LEN: usize = 20 + 32;

impl<E: Engine> IntoBytes<E> for L1AuthorizationPubdata<E> {
    fn encoding_len() -> usize {
        L1_AUTH_DATA_ENCODING_LEN
    }
    fn into_be_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut result = vec![];

        let address_encoding = num_into_bytes_be(cs, self.address.inner, 160)?;
        result.extend(address_encoding);
        result.extend_from_slice(&self.message_hash.inner);

        assert_eq!(result.len(), Self::encoding_len());

        Ok(result)
    }
}
