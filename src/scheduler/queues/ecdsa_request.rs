use super::*;
use cs_derive::*;

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
)]
#[derivative(Clone, Debug)]
pub struct EcdsaVerificationRecord<E: Engine> {
    pub address: UInt160<E>,
    pub message: Bytes32<E>,
}

impl<E: Engine> EcdsaVerificationRecord<E> {
    pub fn empty() -> Self {
        Self {
            address: UInt160::zero(),
            message: Bytes32::empty(),
        }
    }
}

pub(crate) const ECDSA_VERIFICATION_RECORD_ENCODING_LEN: usize =
    __ecdsaverificationrecord_circuit_encoding_len_inner;
