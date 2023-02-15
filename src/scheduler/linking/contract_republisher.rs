use super::*;
use cs_derive::*;

// Takes a contract code and rehashes are sha256
// #[derive(Derivative, CSAllocatable, CSWitnessable, CSEqual, CSSelectable, FixedLengthEncodableExt, FixedLengthDecodableExt)]
// #[EncodingLength = "3"]
// #[PackWithCS = "true"]

#[derive(Derivative, CSAllocatable, CSWitnessable, CSEqual, CSSelectable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct ContractRepublisherStructuredInput<E: Engine> {
    pub code_root: Num<E>,
    pub sha256_hash_output: Bytes32<E>,
}

pub(crate) const CONTRACT_CODE_REPUBLISHER_INPUT_ENCODING_LEN: usize = __contractrepublisherstructuredinput_circuit_encoding_len_inner;
