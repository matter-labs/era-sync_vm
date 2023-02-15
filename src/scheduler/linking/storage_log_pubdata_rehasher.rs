use super::*;
use cs_derive::*;

// Takes a log of storage writes into the rollup accounts and produces a public data required
// to restore the state
#[derive(Derivative, CSAllocatable, CSWitnessable, CSEqual, CSSelectable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct StorageLogWriterRehasherStructuredInput<E: Engine> {
    pub queue_tail: Num<E>,
    pub queue_length: UInt32<E>,
    pub sha256_hash_output: Bytes32<E>,
}

pub(crate) const ROLLUP_STORAGE_PUBDATA_REHASHER_INPUT_ENCODING_LEN: usize = __storagelogwriterrehasherstructuredinput_circuit_encoding_len_inner;
