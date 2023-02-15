use super::*;
use cs_derive::*;

use crate::scheduler::circuit::input::*;

// Takes storage logs with aux byte == precompile and performs 
// demultiplexing into logs of different callers and potentially different shards

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct PerShardAndCallerLogDemultiplexorStructuredInput<E: Engine> {
    pub input_queue_tail: Num<E>,
    pub input_queue_length: UInt32<E>,
    pub shard_ids_outputs: [Byte<E>; NUM_SORTED_PRECOMPILE_OUTPUTS],
    pub queue_tails_outputs: [Num<E>; NUM_SORTED_PRECOMPILE_OUTPUTS],
    pub queue_lengths_outputs: [UInt32<E>; NUM_SORTED_PRECOMPILE_OUTPUTS],
}
