use super::*;
use super::super::queues::*;

// We want to have some context that allows us to at least keep queues inside of it

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct SchedulerContext<E: Engine>{
    // marks whether zkporter is available or not (for exodus purposes mainly)
    pub zkporter_is_available: Boolean,

    // global RAM access queue
    pub memory_queue: MemoryAccessQueue<E, 2, 3>,

    // main log of all state-modifying and write-like operations
    pub storage_log_queue: StorageLogQueue<E>,

    // L1 authorizaiton data (address + message hash)
    pub l1_authorization_pubdata_queue: L1AuthorizationsQueue<E>,

    // request publish the contracts deployed in rollup with rehashing
    pub rollup_contract_code_publishing_queue: NewCodeArgumentOfKnowledgeQueue<E>,

    // request Ethereum EcDSA signature verification 
    pub ecdsa_verification_queue: EcdsaVerificationQueue<E>,

    // request to rehash the transaction information to
    pub eip172_rehashing_queue: Eip712RehashingQueue<E>,

    // request to witness a repacking of some legacy TX as a canonical TX
    pub rlp_recoding_queue: RlpRecodingRequestsQueue<E>,

    // queue of all kinds of requests for providing a verification proof
    pub recursive_verification_requests_queue: RecursiveVerificationRequestQueue<E>,

    // queue to require an operator to demonstrate that he knows a content of
    // newly deployed contract's code root
    pub code_hash_proof_of_knowledge_queue: NewCodeArgumentOfKnowledgeQueue<E>,

    // block number
    pub block_number: UInt64<E>,

    // block timestamp
    pub block_timestamp: UInt64<E>,
}

impl<E: Engine> SchedulerContext<E> {
    pub fn new() -> Self {
        Self {
            zkporter_is_available: Boolean::constant(false),
            memory_queue: MemoryAccessQueue::<E, 2, 3>::empty(),
            storage_log_queue: StorageLogQueue::<E>::empty(),
            l1_authorization_pubdata_queue: L1AuthorizationsQueue::<E>::empty(),
            rollup_contract_code_publishing_queue: NewCodeArgumentOfKnowledgeQueue::<E>::empty(),
            ecdsa_verification_queue: EcdsaVerificationQueue::<E>::empty(),
            eip172_rehashing_queue: Eip712RehashingQueue::<E>::empty(),
            rlp_recoding_queue: RlpRecodingRequestsQueue::<E>::empty(),
            recursive_verification_requests_queue: RecursiveVerificationRequestQueue::<E>::empty(),
            code_hash_proof_of_knowledge_queue: NewCodeArgumentOfKnowledgeQueue::<E>::empty(),
            block_number: UInt64::<E>::zero(),
            block_timestamp: UInt64::<E>::zero(),
        }
    }
}