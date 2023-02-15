use super::*;

pub mod code_factory_processing;
pub mod code_knowledge;
pub mod contract_creation;
pub mod decommit_query;
pub mod delegated_memory_write;
pub mod ecdsa_request;
pub mod full_sponge_like_queue_state;
pub mod l1_authorizations;
pub mod memory_access;
pub mod pubdata_chunk;
pub mod queue_state;
pub mod recursive_request;
pub mod sponge_like_queue_state;
pub mod storage_log;
pub mod withdraw_pubdata;

pub use self::code_factory_processing::*;
pub use self::code_knowledge::*;
pub use self::contract_creation::*;
pub use self::decommit_query::*;
pub use self::delegated_memory_write::*;
pub use self::ecdsa_request::*;
pub use self::full_sponge_like_queue_state::*;
pub use self::l1_authorizations::*;
pub use self::memory_access::*;
pub use self::pubdata_chunk::*;
pub use self::queue_state::*;
pub use self::recursive_request::*;
pub use self::sponge_like_queue_state::*;
pub use self::storage_log::*;
pub use self::withdraw_pubdata::*;

pub use crate::glue::optimizable_queue::FixedWidthEncodingGenericQueueWitness;
pub use crate::glue::sponge_like_optimizable_queue::*;
use crate::vm::primitives::*;

pub type StorageLogQueue<E> = FixedWidthEncodingGenericQueue<E, StorageLogRecord<E>, 5>;
pub type StorageLogQueueWithUnderlyingU32<E> =
    FixedWidthEncodingGenericQueue<E, StorageLogRecordWithUnderlyingU32<E>, 5>;
pub type SortedStorageItemsQueue<E> = FixedWidthEncodingGenericQueue<
    E,
    SortedStorageLogItem<E>,
    SORTED_STORAGE_LOG_RECORD_ENCODING_LEN,
>;
pub type SortedEventItemsQueue<E> =
    FixedWidthEncodingGenericQueue<E, SortedEventLogItem<E>, SORTED_EVENT_LOG_RECORD_ENCODING_LEN>;
pub type RecursiveVerificationRequestQueue<E> =
    FixedWidthEncodingGenericQueue<E, RecursiveRequest<E>, 2>;
pub type MemoryAccessQueue<E, const AWIDTH: usize, const SWIDTH: usize> =
    FixedWidthEncodingSpongeLikeQueue<E, RawMemoryQuery<E>, 2, AWIDTH, SWIDTH>;
pub type DecommitmentRequestsQueue<E, const AWIDTH: usize, const SWIDTH: usize> =
    FixedWidthEncodingSpongeLikeQueue<E, DecommitmentRequest<E>, 2, AWIDTH, SWIDTH>;
