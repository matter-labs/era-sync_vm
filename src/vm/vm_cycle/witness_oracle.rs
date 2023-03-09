use super::*;

use crate::glue::code_unpacker_sha256::memory_query_updated::RawMemoryQuery;
use crate::scheduler::data_access_functions::StorageLogRecord;
use crate::scheduler::queues::{DecommitQuery, DecommitQueryWitness};
use crate::vm::vm_cycle::memory::MemoryLocation;
use crate::vm::vm_cycle::memory_view::write_query::MemoryWriteQuery;
use crate::vm::vm_state::saved_contract_context::{
    ExecutionContextRecord, ExecutionContextRecordWitness,
};

#[derive(Derivative)]
#[derivative(Clone, Debug, Default)]
pub struct MemoryWitness {
    pub value: BigUint,
    pub is_ptr: bool,
}

pub trait WitnessOracle<E: Engine>:
    'static + Default + Clone + serde::Serialize + serde::de::DeserializeOwned
{
    fn get_memory_witness_for_read(
        &mut self,
        timestamp: UInt32<E>,
        key: &MemoryLocation<E>,
        execute: &Boolean,
    ) -> Option<MemoryWitness>;
    fn push_memory_witness(&mut self, memory_query: &MemoryWriteQuery<E>, execute: &Boolean);
    fn get_storage_read_witness(
        &mut self,
        key: &StorageLogRecord<E>,
        needs_witness: &Boolean,
        execute: &Boolean,
    ) -> Option<BigUint>;
    fn get_refunds(
        &mut self,
        key: &StorageLogRecord<E>,
        is_write: &Boolean,
        execute: &Boolean,
    ) -> Option<u32>;
    fn push_storage_witness(
        &mut self,
        key: &StorageLogRecord<E>,
        is_write: &Boolean,
        execute: &Boolean,
    );
    fn get_rollback_queue_witness(
        &mut self,
        key: &StorageLogRecord<E>,
        execute: &Boolean,
    ) -> Option<E::Fr>;
    fn get_rollback_queue_tail_witness_for_call(
        &mut self,
        timestamp: UInt32<E>,
        execute: &Boolean,
    ) -> Option<E::Fr>;
    fn report_new_callstack_frame(
        &mut self,
        new_callstack: &ExecutionContextRecord<E>,
        new_depth: UInt32<E>,
        is_call: &Boolean,
        execute: &Boolean,
    );
    fn push_callstack_witness(
        &mut self,
        current_record: &ExecutionContextRecord<E>,
        current_depth: &UInt32<E>,
        execute: &Boolean,
    );
    fn get_callstack_witness(
        &mut self,
        execute: &Boolean,
        depth: &UInt32<E>,
    ) -> (Option<ExecutionContextRecordWitness<E>>, Option<[E::Fr; 3]>);
    fn get_decommittment_request_witness(
        &mut self,
        request: &DecommitQuery<E>,
        execute: &Boolean,
    ) -> Option<DecommitQueryWitness<E>>;
    fn at_completion(self) {}
}

use crate::vm::primitives::u160;
use std::collections::HashMap;

pub fn u256_to_biguint(value: zk_evm::ethereum_types::U256) -> BigUint {
    let mut result = BigUint::from(0u64);
    result += BigUint::from(value.0[3]);
    result <<= 64;
    result += BigUint::from(value.0[2]);
    result <<= 64;
    result += BigUint::from(value.0[1]);
    result <<= 64;
    result += BigUint::from(value.0[0]);

    result
}
