use super::*;

// take a queue from StorageApplicationStage0StructuredInput and apply real storage log transitions. 
// Log all writes to Rollup accounts to later on repack as public data
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct StorageApplicationStage1StructuredInput<E: Engine> {
    pub zkporter_is_available: Boolean,
    pub sorted_accounts_roots_queue_tail: Num<E>,
    pub sorted_accounts_roots_queue_length: UInt32<E>,
    pub sorted_storage_records_queue_tail: Num<E>,
    pub sorted_storage_records_queue_length: UInt32<E>,
    pub rollup_writes_queue_tail: Num<E>,
    pub rollup_writes_queue_length: UInt32<E>,
}
