use super::*;

// this queue unwraps a storage completely and for some set of account (witnesses)
// and their transitions initial -> final root and rollup/porter markers
// outputs a queue of tuples (account, rollup/porter, initial storage root, final storage root)
// Next circuit will pick up this queue and apply real storage log requests making initial -> final root transitions
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct StorageApplicationStage0StructuredInput<E: Engine> {
    pub zkporter_is_available: Boolean,
    pub initial_root: Num<E>,
    pub final_root: Num<E>,
    pub queue_tail: Num<E>,
    pub queue_length: UInt32<E>,
}
