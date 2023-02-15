use super::*;
use cs_derive::*;

// Takes a log of auxilary pubdata produced by various sources and rehashes it
#[derive(Derivative, CSAllocatable, CSWitnessable, CSEqual, CSSelectable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct AuxPubdataRehasherStructuredInput<E: Engine> {
    pub queue_tail: Num<E>,
    pub queue_length: UInt32<E>,
    pub sha256_hash_output: Bytes32<E>
}

pub(crate) const AUX_PUBDATA_REHASHER_INPUT_ENCODING_LEN: usize = __auxpubdatarehasherstructuredinput_circuit_encoding_len_inner;

impl<E: Engine> AuxPubdataRehasherStructuredInput<E> {
    pub fn empty() -> Self {
        Self {
            queue_tail: Num::<E>::zero(),
            queue_length: UInt32::<E>::zero(),
            sha256_hash_output: Bytes32::<E>::empty()
        }
    }
}


