use super::*;
use cs_derive::*;

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct DemultiplexorStructuredLogicalOutput<E: Engine> {
    pub rollup_storage_queue_tail: Num<E>,
    pub rollup_storage_queue_num_items: UInt32<E>,
    pub porter_storage_queue_tail: Num<E>,
    pub porter_storage_queue_num_items: UInt32<E>,
    pub events_queue_tail: Num<E>,
    pub events_queue_num_items: UInt32<E>,
    pub l1_messages_queue_tail: Num<E>,
    pub l1_messages_queue_num_items: UInt32<E>,
    pub keccak_calls_queue_tail: Num<E>,
    pub keccak_calls_queue_num_items: UInt32<E>,
    pub sha256_calls_queue_tail: Num<E>,
    pub sha256_calls_queue_num_items: UInt32<E>,
    pub ecdsa_calls_queue_tail: Num<E>,
    pub ecdsa_calls_queue_num_items: UInt32<E>,
}

// Takes a raw storage log and performs demultiplexing into storage logs of different kinds

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct LogDemultiplexorStructuredInput<E: Engine> {
    pub input_queue_tail: Num<E>,
    pub input_queue_length: UInt32<E>,
    pub output_data: DemultiplexorStructuredLogicalOutput<E>
}