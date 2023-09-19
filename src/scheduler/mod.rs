use super::*;
use cs_derive::*;
use zkevm_opcode_defs::BOOTLOADER_CODE_PAGE;

use crate::bellman::SynthesisError;
use crate::data_structures::markers::*;
use crate::derivative::*;
use crate::ff::*;
use crate::glue::code_unpacker_sha256::memory_query_updated::*;
use crate::pairing::*;
use crate::vm::primitives::UInt128;
use crate::vm::vm_cycle::memory_view::read_view::MemoryReadQuery;
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::custom_rescue_gate::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::plonk::circuit::Assignment;
use franklin_crypto::rescue::*;

use crate::bellman::plonk::better_better_cs::cs::*;
use crate::circuit_structures::bytes32::*;
use crate::circuit_structures::traits::*;
use crate::circuit_structures::utils::*;
use crate::circuit_structures::*;
use crate::data_structures::markers::*;
use crate::glue::optimizable_queue::*;
use crate::glue::sponge_like_optimizable_queue::*;
use crate::glue::traits::*;
use crate::traits::*;
use crate::utils::*;
use crate::vm::optimizer::*;
use crate::vm::partitioner::{smart_and, smart_or};
use crate::vm::primitives::uint256::*;
use crate::vm::primitives::utils::*;
use crate::vm::primitives::{UInt16, UInt32, UInt64};
use crate::vm::structural_eq::*;
use cs_derive::*;
use franklin_crypto::plonk::circuit::bigint::bigint::*;
use franklin_crypto::plonk::circuit::byte::*;
use franklin_crypto::plonk::circuit::permutation_network::*;
use num_bigint::BigUint;

use crate::vm::primitives::UInt8;

pub mod circuit;
pub mod constants;
pub mod data_access_functions;
pub mod ext;
pub mod queues;
// pub mod linking;
pub mod block_header;

// pub use self::linking::*;
pub use self::constants::*;
use self::queues::DecommitQueue;
use self::queues::*;

use std::array::IntoIter;
use std::collections::HashMap;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(u8)]
pub enum CircuitType {
    Scheduler = 0,
    IntermidiateNode = 1,
    Leaf = 2,
    VM = 3,
    DecommitmentsFilter = 4,
    Decommiter = 5,
    LogDemultiplexer = 6,
    KeccakPrecompile = 7,
    Sha256Precompile = 8,
    EcrecoverPrecompile = 9,
    RamValidation = 10,
    StorageFilter = 11,
    StorageApplicator = 12,
    StorageFreshWritesHasher = 13,
    StorageRepeatedWritesHasher = 14,
    EventsRevertsFilter = 15,
    L1MessagesRevertsFilter = 16,
    L1MessagesHasher = 17,
    L1MessagesMerkelization = 18,
    EventsMerkelization = 19,
    None = 20,
}

pub const NUM_CIRCUIT_TYPES_TO_SCHEDULE: usize = 16;
pub const SCHEDULER_TIMESTAMP: u32 = 1;

pub const NUM_MEMORY_QUERIES_TO_VERIFY: usize = 1;
pub const PREVIOUS_BLOCK_HASH_QUERY_KEY: &'static str = "previous_block_hash";
pub const PREVIOUS_BLOCK_HASH_HEAP_SLOT: u32 = 0;
pub const MEMORY_QUERIES_MAP: [(&'static str, u32); NUM_MEMORY_QUERIES_TO_VERIFY] =
    [(PREVIOUS_BLOCK_HASH_QUERY_KEY, PREVIOUS_BLOCK_HASH_HEAP_SLOT)];

#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct RecursiveProofQuery<E: Engine> {
    pub cicruit_type: UInt8<E>,
    pub closed_form_input_hash: Num<E>,
}

pub type RecursiveProofQueue<E> = FixedWidthEncodingGenericQueue<E, RecursiveProofQuery<E>, 2>;

use crate::inputs::*;

use crate::glue::code_unpacker_sha256::input::*;
use crate::glue::demux_log_queue::input::*;
use crate::glue::ecrecover_circuit::input::*;
use crate::glue::keccak256_round_function_circuit::input::*;
use crate::glue::log_sorter::input::*;
use crate::glue::merkleize_l1_messages::input::*;
use crate::glue::pubdata_hasher::input::*;
use crate::glue::sha256_round_function_circuit::input::*;
use crate::glue::sort_decommittment_requests::input::*;
use crate::glue::storage_application::input::*;
use crate::glue::storage_validity_by_grand_product::input::*;
use crate::recursion::node_aggregation::*;
use crate::scheduler::block_header::*;
use crate::vm::vm_cycle::input::*;

// NOTE: This is pure "witness" - we do not want to allocate it all at once

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct SchedulerCircuitInstanceWitness<E: Engine> {
    pub prev_block_data: BlockPassthroughDataWitness<E>,
    pub block_meta_parameters: BlockMetaParametersWitness<E>,

    // passthrough outputs for all the circuits that produce such
    pub vm_end_of_execution_observable_output: VmOutputDataWitness<E>,
    pub decommits_sorter_observable_output: CodeDecommittmentsDeduplicatorOutputDataWitness<E>,
    pub code_decommitter_observable_output: CodeDecommitterOutputDataWitness<E>,
    pub log_demuxer_observable_output: LogDemuxerOutputDataWitness<E>,
    pub keccak256_observable_output: PrecompileFunctionOutputDataWitness<E>,
    pub sha256_observable_output: PrecompileFunctionOutputDataWitness<E>,
    pub ecrecover_observable_output: PrecompileFunctionOutputDataWitness<E>,
    // RAM permutation doesn't produce anything
    pub storage_sorter_observable_output: StorageDeduplicatorOutputDataWitness<E>,
    pub storage_application_observable_output: StorageApplicationOutputDataWitness<E>,
    pub initial_writes_rehasher_observable_output: PubdataHasherOutputDataWitness<E>,
    pub repeated_writes_rehasher_observable_output: PubdataHasherOutputDataWitness<E>,
    pub events_sorter_observable_output: EventsDeduplicatorOutputDataWitness<E>,
    pub l1messages_sorter_observable_output: EventsDeduplicatorOutputDataWitness<E>,
    pub l1messages_linear_hasher_observable_output: PubdataHasherOutputDataWitness<E>,
    pub l1messages_merklizer_observable_output: MessagesMerklizerOutputDataWitness<E>,

    // very few things that we need to properly produce this block
    pub storage_log_tail: E::Fr,
    // pub memory_queries_to_verify: [MemoryQueryWitness<E>; NUM_MEMORY_QUERIES_TO_VERIFY],
    pub per_circuit_closed_form_inputs: Vec<ClosedFormInputCompactFormWitness<E>>,

    pub bootloader_heap_memory_state: SpongeLikeQueueStateWitness<E, 3>,
    pub ram_sorted_queue_state: SpongeLikeQueueStateWitness<E, 3>,
    pub decommits_sorter_intermediate_queue_state: SpongeLikeQueueStateWitness<E, 3>,

    // all multi-circuits responsible for sorting
    pub rollup_storage_sorter_intermediate_queue_state:
        FixedWidthEncodingGenericQueueStateWitness<E>,
    pub events_sorter_intermediate_queue_state: FixedWidthEncodingGenericQueueStateWitness<E>,
    pub l1messages_sorter_intermediate_queue_state: FixedWidthEncodingGenericQueueStateWitness<E>,

    pub rollup_initital_writes_pubdata_hash: Bytes32Witness<E>,
    pub rollup_repeated_writes_pubdata_hash: Bytes32Witness<E>,

    // extra information about the previous block
    pub previous_block_meta_hash: Bytes32Witness<E>,
    pub previous_block_aux_hash: Bytes32Witness<E>,

    // extra information about our recursion tree
    pub recursion_node_verification_key_hash: Bytes32Witness<E>,
    pub recursion_leaf_verification_key_hash: Bytes32Witness<E>,
    pub all_different_circuits_keys_hash: Bytes32Witness<E>,
    pub aggregation_result: NodeAggregationOutputDataWitness<E>,

    #[derivative(Debug = "ignore")]
    pub proof_witnesses: Vec<ZkSyncParametricProof<E>>,

    pub vk_encoding_witnesses: Vec<Vec<E::Fr>>,
}

use crate::precompiles::*;

#[track_caller]
fn compute_precompile_commitment<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    precompile_queue_state: &FixedWidthEncodingGenericQueueState<E>,
    mem_queue_state_before: &FullSpongeLikeQueueState<E>,
    mem_queue_state_after: &FullSpongeLikeQueueState<E>,
    round_function: &R,
) -> Result<(Num<E>, Num<E>), SynthesisError> {
    let input_data = PrecompileFunctionInputData::<E> {
        initial_log_queue_state: precompile_queue_state.clone(),
        initial_memory_state: mem_queue_state_before.clone(),
    };
    let input_data_commitment = commit_encodable_item(cs, &input_data, round_function)?;

    let output_data = PrecompileFunctionOutputData::<E> {
        final_memory_state: mem_queue_state_after.clone(),
    };
    let output_data_commitment = commit_encodable_item(cs, &output_data, round_function)?;

    Ok((input_data_commitment, output_data_commitment))
}

#[track_caller]
fn compute_filter_circuit_commitment<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    queue_state_before: &FixedWidthEncodingGenericQueueState<E>,
    intermediate_queue_state: &FixedWidthEncodingGenericQueueState<E>,
    queue_state_after: &FixedWidthEncodingGenericQueueState<E>,
    round_function: &R,
) -> Result<(Num<E>, Num<E>), SynthesisError> {
    // We use here the naming events_deduplicator but the function is applicable for
    // storage deduplicator is well - may be we should make this fact more observable
    let input_data = EventsDeduplicatorInputData::<E> {
        initial_log_queue_state: queue_state_before.clone(),
        intermediate_sorted_queue_state: intermediate_queue_state.clone(),
    };
    let input_data_commitment = commit_encodable_item(cs, &input_data, round_function)?;

    let output_data = EventsDeduplicatorOutputData::<E> {
        final_queue_state: queue_state_after.clone(),
    };
    let output_data_commitment = commit_encodable_item(cs, &output_data, round_function)?;

    Ok((input_data_commitment, output_data_commitment))
}

#[track_caller]
fn compute_merkelization_circuit_commitment<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    queue_state: &FixedWidthEncodingGenericQueueState<E>,
    linear_hash: &Bytes32<E>,
    root_hash: &Bytes32<E>,
    round_function: &R,
) -> Result<(Num<E>, Num<E>), SynthesisError> {
    let input_data = MessagesMerklizerInputData::<E> {
        input_queue_state: queue_state.clone(),
    };
    let input_data_commitment = commit_encodable_item(cs, &input_data, round_function)?;

    let output_data = MessagesMerklizerOutputData::<E> {
        linear_hash: linear_hash.clone(),
        root_hash: root_hash.clone(),
    };
    let output_data_commitment = commit_encodable_item(cs, &output_data, round_function)?;

    Ok((input_data_commitment, output_data_commitment))
}

#[track_caller]
fn compute_storage_applicator_circuit_commitment<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    storage_queue_state: &FixedWidthEncodingGenericQueueState<E>,
    initial_root: &Bytes32<E>,
    initial_enumeration_counter: &UInt64<E>,
    final_root: &[UInt128<E>; 2],
    final_enumeration_counter: &UInt64<E>,
    repeated_writes_queue_state: &FixedWidthEncodingGenericQueueState<E>,
    initital_writes_queue_state: &FixedWidthEncodingGenericQueueState<E>,
    shard_id: u8,
    round_function: &R,
) -> Result<(Num<E>, Num<E>), SynthesisError> {
    let initial_root = UInt256::from_le_bytes_fixed(cs, &initial_root.inner)?;

    let initial_block_header_as_u128x2 = AsU128x2::<E>::from_uint256(cs, &initial_root)?;
    let final_block_header_as_u128x2 = AsU128x2 { inner: *final_root };

    let input_data = StorageApplicationInputData::<E> {
        initial_next_enumeration_counter: *initial_enumeration_counter,
        shard: UInt8::<E>::from_uint(shard_id),
        initial_root: initial_block_header_as_u128x2.inner,
        storage_application_log_state: storage_queue_state.clone(),
    };
    let input_data_commitment = commit_encodable_item(cs, &input_data, round_function)?;

    let output_data = StorageApplicationOutputData::<E> {
        final_next_enumeration_counter: *final_enumeration_counter,
        final_root: final_block_header_as_u128x2.inner,
        repeated_writes_pubdata_queue_state: repeated_writes_queue_state.clone(),
        initial_writes_pubdata_queue_state: initital_writes_queue_state.clone(),
    };
    let output_data_commitment = commit_encodable_item(cs, &output_data, round_function)?;

    Ok((input_data_commitment, output_data_commitment))
}

#[track_caller]
fn compute_pubdata_hasher_circuit_commitment<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    input_queue_state: &FixedWidthEncodingGenericQueueState<E>,
    pubdata_hash: &Bytes32<E>,
    round_function: &R,
) -> Result<(Num<E>, Num<E>), SynthesisError> {
    let input_data = PubdataHasherInputData::<E> {
        input_queue_state: input_queue_state.clone(),
    };
    let input_data_commitment = commit_encodable_item(cs, &input_data, round_function)?;

    let output_data = PubdataHasherOutputData::<E> {
        pubdata_hash: pubdata_hash.clone(),
    };
    let output_data_commitment = commit_encodable_item(cs, &output_data, round_function)?;

    Ok((input_data_commitment, output_data_commitment))
}

#[track_caller]
fn validate_circuit_commitment<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    exec_flag: &Boolean,
    actual_circ_type: &UInt8<E>,
    sample_circuit_type: &CircuitType,
    actual_commitment: &Num<E>,
    sample_commitment: &Num<E>,
) -> Result<(), SynthesisError> {
    // we check that (actual_commitment == sample_commitment) in the case flag is set and
    // actual circuit type is equivalen to sample one
    let circ_types_are_equal = UInt8::equals(
        cs,
        &actual_circ_type,
        &UInt8::from_uint(*sample_circuit_type as u8),
    )?;
    let validation_flag = Boolean::and(cs, &exec_flag, &circ_types_are_equal)?;
    let commitments_are_equal = Num::equals(cs, &actual_commitment, &sample_commitment)?;
    can_not_be_false_if_flagged(cs, &commitments_are_equal, &validation_flag)
}

use crate::recursion::recursion_tree::AggregationParameters;
use crate::recursion::recursion_tree::NUM_LIMBS;
use crate::recursion::transcript::GenericTranscriptGadget;
use franklin_crypto::plonk::circuit::bigint::RnsParameters;
use rescue_poseidon::RescueParams;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
pub struct BlockApplicationWitness<E: Engine> {
    pub passthrough_data_part: BlockPassthroughDataWitness<E>,
    pub passthrough_data_hash: [u8; 32],
    pub aux_data_part: BlockAuxilaryOutputWitness<E>,
    pub aux_data_hash: [u8; 32],
    pub meta_data_part: BlockMetaParametersWitness<E>,
    pub meta_data_hash: [u8; 32],
    pub block_header_hash: [u8; 32],
    pub aggregation_result_coords: [[u8; 32]; 4],
    pub committment_bytes: [u8; 32],
}

pub fn scheduler_function<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<SchedulerCircuitInstanceWitness<E>>,
    reporting_function: Option<Box<dyn FnOnce(BlockApplicationWitness<E>) -> ()>>,
    round_function: &R,
    params: (
        u32,
        RnsParameters<E, E::Fq>,
        AggregationParameters<
            E,
            GenericTranscriptGadget<E, RescueParams<E, 2, 3>, 2, 3>,
            RescueParams<E, 2, 3>,
            2,
            3,
        >,
        [E::Fr; VK_ENCODING_LENGTH],
        ZkSyncParametricProof<E>,
        Option<[E::G2Affine; 2]>,
    ),
) -> Result<AllocatedNum<E>, SynthesisError> {
    let (limit, rns_params, aggregation_params, padding_vk_encoding, padding_proof, g2_elements) =
        params;

    use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
    use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    let columns3 = vec![
        PolyIdentifier::VariablesPolynomial(0),
        PolyIdentifier::VariablesPolynomial(1),
        PolyIdentifier::VariablesPolynomial(2),
    ];

    if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
        let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            BitwiseLogicTable::new(&name, 8),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(bitwise_logic_table)?;
    };

    inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    let prev_block_data = project_ref!(witness, prev_block_data).cloned();
    let prev_block_data = BlockPassthroughData::alloc_from_witness(cs, prev_block_data)?;

    let block_meta_parameters = project_ref!(witness, block_meta_parameters).cloned();
    let block_meta_parameters = BlockMetaParameters::alloc_from_witness(cs, block_meta_parameters)?;

    Boolean::enforce_equal(
        cs,
        &block_meta_parameters.zkporter_is_available,
        &Boolean::constant(false),
    )?;

    // create initial queues

    let mut recursive_queue = RecursiveProofQueue::empty();

    let bootloader_heap_memory_state = project_ref!(witness, bootloader_heap_memory_state).cloned();
    let bootloader_heap_memory_state =
        SpongeLikeQueueState::alloc_from_witness(cs, bootloader_heap_memory_state)?;

    let mut initial_memory_queue_state = FullSpongeLikeQueueState::empty();
    initial_memory_queue_state.tail = bootloader_heap_memory_state.sponge_state;
    initial_memory_queue_state.length = bootloader_heap_memory_state.length;

    let memory_queue = MemoryQueriesQueue::from_state(cs, initial_memory_queue_state)?;

    let mut decommittments_queue = DecommitQueue::empty();
    use crate::scheduler::queues::*;
    let bootloader_code_hash = block_meta_parameters.bootloader_code_hash.inner;
    let bootloader_code_hash = UInt256::from_be_bytes_fixed(cs, &bootloader_code_hash)?;
    let bootloader_decommittment_query = DecommitQuery {
        root_hash: DecommitHash::AsU256(bootloader_code_hash),
        page: UInt32::from_uint(BOOTLOADER_CODE_PAGE),
        is_first: Boolean::constant(true),
        timestamp: UInt32::from_uint(SCHEDULER_TIMESTAMP),
    };

    let _ = decommittments_queue.push(
        cs,
        &bootloader_decommittment_query,
        &Boolean::constant(true),
        round_function,
    )?;
    // now we can run all the cirucits in sequence

    let mut execution_stage_bitmask = [Boolean::constant(false); NUM_CIRCUIT_TYPES_TO_SCHEDULE];
    execution_stage_bitmask[0] = Boolean::constant(true); // VM
                                                          // let mut scheduling_complete =  Boolean::constant(false);

    // create all the intermediate output data in uncommitted form to later check for equality

    let vm_end_of_execution_observable_output =
        project_ref!(witness, vm_end_of_execution_observable_output).cloned();
    let vm_end_of_execution_observable_output =
        VmOutputData::alloc_from_witness(cs, vm_end_of_execution_observable_output)?;

    let decommits_sorter_observable_output =
        project_ref!(witness, decommits_sorter_observable_output).cloned();
    let decommits_sorter_observable_output =
        CodeDecommittmentsDeduplicatorOutputData::alloc_from_witness(
            cs,
            decommits_sorter_observable_output,
        )?;

    let code_decommitter_observable_output =
        project_ref!(witness, code_decommitter_observable_output).cloned();
    let code_decommitter_observable_output =
        CodeDecommitterOutputData::alloc_from_witness(cs, code_decommitter_observable_output)?;

    let log_demuxer_observable_output =
        project_ref!(witness, log_demuxer_observable_output).cloned();
    let log_demuxer_observable_output =
        LogDemuxerOutputData::alloc_from_witness(cs, log_demuxer_observable_output)?;

    let keccak256_observable_output = project_ref!(witness, keccak256_observable_output).cloned();
    let keccak256_observable_output =
        PrecompileFunctionOutputData::alloc_from_witness(cs, keccak256_observable_output)?;

    let sha256_observable_output = project_ref!(witness, sha256_observable_output).cloned();
    let sha256_observable_output =
        PrecompileFunctionOutputData::alloc_from_witness(cs, sha256_observable_output)?;

    let ecrecover_observable_output = project_ref!(witness, ecrecover_observable_output).cloned();
    let ecrecover_observable_output =
        PrecompileFunctionOutputData::alloc_from_witness(cs, ecrecover_observable_output)?;

    let storage_sorter_observable_output =
        project_ref!(witness, storage_sorter_observable_output).cloned();
    let storage_sorter_observable_output =
        StorageDeduplicatorOutputData::alloc_from_witness(cs, storage_sorter_observable_output)?;

    let storage_application_observable_output =
        project_ref!(witness, storage_application_observable_output).cloned();
    let storage_application_observable_output = StorageApplicationOutputData::alloc_from_witness(
        cs,
        storage_application_observable_output,
    )?;

    let events_sorter_observable_output =
        project_ref!(witness, events_sorter_observable_output).cloned();
    let events_sorter_observable_output =
        EventsDeduplicatorOutputData::alloc_from_witness(cs, events_sorter_observable_output)?;

    let l1messages_sorter_observable_output =
        project_ref!(witness, l1messages_sorter_observable_output).cloned();
    let l1messages_sorter_observable_output =
        EventsDeduplicatorOutputData::alloc_from_witness(cs, l1messages_sorter_observable_output)?;

    let l1messages_linear_hasher_observable_output =
        project_ref!(witness, l1messages_linear_hasher_observable_output).cloned();
    let l1messages_linear_hasher_observable_output = PubdataHasherOutputData::alloc_from_witness(
        cs,
        l1messages_linear_hasher_observable_output,
    )?;

    let l1messages_merklizer_observable_output =
        project_ref!(witness, l1messages_merklizer_observable_output).cloned();
    let l1messages_merklizer_observable_output = MessagesMerklizerOutputData::alloc_from_witness(
        cs,
        l1messages_merklizer_observable_output,
    )?;

    // auxilary intermediate states
    let rollup_storage_sorter_intermediate_queue_state =
        project_ref!(witness, rollup_storage_sorter_intermediate_queue_state).cloned();
    let rollup_storage_sorter_intermediate_queue_state =
        FixedWidthEncodingGenericQueueState::alloc_from_witness(
            cs,
            rollup_storage_sorter_intermediate_queue_state,
        )?;

    let events_sorter_intermediate_queue_state =
        project_ref!(witness, events_sorter_intermediate_queue_state).cloned();
    let events_sorter_intermediate_queue_state =
        FixedWidthEncodingGenericQueueState::alloc_from_witness(
            cs,
            events_sorter_intermediate_queue_state,
        )?;

    let l1messages_sorter_intermediate_queue_state =
        project_ref!(witness, l1messages_sorter_intermediate_queue_state).cloned();
    let l1messages_sorter_intermediate_queue_state =
        FixedWidthEncodingGenericQueueState::alloc_from_witness(
            cs,
            l1messages_sorter_intermediate_queue_state,
        )?;

    // final VM storage log state for our construction
    let storage_log_tail = Num::alloc(cs, project_ref!(witness, storage_log_tail).cloned())?;

    // form the VM input
    let default_aa_code_hash =
        UInt256::from_be_bytes_fixed(cs, &block_meta_parameters.default_aa_code_hash.inner)?;

    use crate::vm::vm_state::GlobalContext;
    let global_context = GlobalContext {
        zkporter_is_available: block_meta_parameters.zkporter_is_available,
        default_aa_code_hash,
    };

    // we can form all the observable inputs already as those are just functions of observable outputs

    let vm_observable_input = VmInputData {
        rollback_queue_tail_for_block: storage_log_tail,
        memory_queue_initial_state: memory_queue.into_state(),
        decommitment_queue_initial_state: decommittments_queue.into_state(),
        per_block_context: global_context,
    };
    let vm_observable_input_commitment =
        commit_variable_length_encodable_item(cs, &vm_observable_input, round_function)?;
    let vm_observable_output_commitment = commit_variable_length_encodable_item(
        cs,
        &vm_end_of_execution_observable_output,
        round_function,
    )?;

    let decommits_sorter_intermediate_queue_state =
        project_ref!(witness, decommits_sorter_intermediate_queue_state).cloned();
    let decommits_sorter_intermediate_queue_state =
        SpongeLikeQueueState::alloc_from_witness(cs, decommits_sorter_intermediate_queue_state)?;
    let mut decommits_sorter_circuit_sorted_queue_state = FullSpongeLikeQueueState::empty();
    decommits_sorter_circuit_sorted_queue_state.tail =
        decommits_sorter_intermediate_queue_state.sponge_state;
    decommits_sorter_circuit_sorted_queue_state.length =
        decommits_sorter_intermediate_queue_state.length;

    let decommittments_sorter_circuit_input = CodeDecommittmentsDeduplicatorInputData::<E> {
        initial_log_queue_state: vm_end_of_execution_observable_output
            .decommitment_queue_final_state,
        sorted_queue_initial_state: decommits_sorter_circuit_sorted_queue_state,
    };
    let decommittments_sorter_circuit_input_commitment =
        commit_encodable_item(cs, &decommittments_sorter_circuit_input, round_function)?;
    let decommittments_sorter_observable_output_commitment =
        commit_encodable_item(cs, &decommits_sorter_observable_output, round_function)?;

    // code decommiments:
    let code_decommitter_circuit_input = CodeDecommitterInputData::<E> {
        memory_queue_initial_state: vm_end_of_execution_observable_output.memory_queue_final_state,
        sorted_requests_queue_initial_state: decommits_sorter_observable_output.final_queue_state,
    };
    let code_decommitter_circuit_input_commitment =
        commit_encodable_item(cs, &code_decommitter_circuit_input, round_function)?;
    let code_decommitter_observable_output_commitment =
        commit_encodable_item(cs, &code_decommitter_observable_output, round_function)?;

    // log demultiplexer
    let log_demux_circuit_input = LogDemuxerInputData::<E> {
        initial_log_queue_state: vm_end_of_execution_observable_output.log_queue_final_state,
    };
    let log_demux_circuit_input_commitment =
        commit_encodable_item(cs, &log_demux_circuit_input, round_function)?;
    let log_demuxer_observable_output_commitment =
        commit_encodable_item(cs, &log_demuxer_observable_output, round_function)?;

    // all intermediate queues for sorters

    // precompiles: keccak, sha256 and ecrecover
    let (keccak_circuit_observable_input_commitment, keccak_circuit_observable_output_commitment) =
        compute_precompile_commitment(
            cs,
            &log_demuxer_observable_output.keccak256_access_queue_state,
            &code_decommitter_observable_output.memory_queue_final_state,
            &keccak256_observable_output.final_memory_state,
            round_function,
        )?;
    let (sha256_circuit_observable_input_commitment, sha256_circuit_observable_output_commitment) =
        compute_precompile_commitment(
            cs,
            &log_demuxer_observable_output.sha256_access_queue_state,
            &keccak256_observable_output.final_memory_state,
            &sha256_observable_output.final_memory_state,
            round_function,
        )?;
    let (
        ecrecover_circuit_observable_input_commitment,
        ecrecover_circuit_observable_output_commitment,
    ) = compute_precompile_commitment(
        cs,
        &log_demuxer_observable_output.ecrecover_access_queue_state,
        &sha256_observable_output.final_memory_state,
        &ecrecover_observable_output.final_memory_state,
        round_function,
    )?;

    // ram permutation and validation
    // NBL this circuit is terminal - it has no actual output

    use crate::glue::memory_queries_validity::ram_permutation_inout::*;

    let ram_sorted_queue_state = project_ref!(witness, ram_sorted_queue_state).cloned();
    let ram_sorted_queue_state =
        SpongeLikeQueueState::alloc_from_witness(cs, ram_sorted_queue_state)?;
    let mut ram_permutation_circuit_sorted_queue_state = FullSpongeLikeQueueState::empty();
    ram_permutation_circuit_sorted_queue_state.tail = ram_sorted_queue_state.sponge_state;
    ram_permutation_circuit_sorted_queue_state.length = ram_sorted_queue_state.length;

    let ram_validation_circuit_input = RamPermutationInputData::<E> {
        unsorted_queue_initial_state: ecrecover_observable_output.final_memory_state,
        sorted_queue_initial_state: ram_permutation_circuit_sorted_queue_state,
        non_deterministic_bootloader_memory_snapshot_length: bootloader_heap_memory_state.length,
    };
    let ram_validation_circuit_input_commitment =
        commit_encodable_item(cs, &ram_validation_circuit_input, round_function)?;

    // events reverts filter and merkelization
    let (events_filter_input_com, events_filter_output_com) = compute_filter_circuit_commitment(
        cs,
        &log_demuxer_observable_output.events_access_queue_state,
        &events_sorter_intermediate_queue_state,
        &events_sorter_observable_output.final_queue_state,
        round_function,
    )?;

    // let (events_merkelizer_input_com, events_merkelizer_output_com) = compute_merkelization_circuit_commitment(
    //     cs,
    //     &filtered_events_queue_state,
    //     &events_linear_hash_as_bytes32,
    //     &events_root_as_bytes32,
    //     round_function
    // )?;

    // l1 messages reverts filter and merkelization
    let (l1_messages_filter_input_com, l1_messages_filter_output_com) =
        compute_filter_circuit_commitment(
            cs,
            &log_demuxer_observable_output.l1messages_access_queue_state,
            &l1messages_sorter_intermediate_queue_state,
            &l1messages_sorter_observable_output.final_queue_state,
            round_function,
        )?;

    let (l1_messages_hasher_input_com, l1_messages_hasher_output_com) =
        compute_pubdata_hasher_circuit_commitment(
            cs,
            &l1messages_sorter_observable_output.final_queue_state,
            &l1messages_linear_hasher_observable_output.pubdata_hash,
            round_function,
        )?;

    let (l1_messages_merkelizer_input_com, l1_messages_merkelizer_output_com) =
        compute_merkelization_circuit_commitment(
            cs,
            &l1messages_sorter_observable_output.final_queue_state,
            &l1messages_merklizer_observable_output.linear_hash,
            &l1messages_merklizer_observable_output.root_hash,
            round_function,
        )?;

    const NUM_PROCESSABLE_SHARDS: usize = 1;

    let mut storage_filter_input_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];
    let mut storage_filter_output_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];
    let mut storage_applicator_input_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];
    let mut storage_applicator_output_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];
    let mut repeated_pubdata_hasher_input_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];
    let mut repeated_pubdata_hasher_output_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];
    let mut initial_pubdata_hasher_input_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];
    let mut initial_pubdata_hasher_output_commitments = [Num::zero(); NUM_PROCESSABLE_SHARDS];

    let storage_queues_state = [log_demuxer_observable_output.storage_access_queue_state];
    let filtered_storage_queues_state = [storage_sorter_observable_output.final_sorted_queue_state];

    let initial_enumeration_counters = [prev_block_data.per_shard_states[0].enumeration_counter];

    let initial_state_roots = [prev_block_data.per_shard_states[0].state_root];

    let final_enumeration_counters =
        [storage_application_observable_output.final_next_enumeration_counter];

    let final_state_roots = [storage_application_observable_output.final_root];

    let initial_writes_queues_states =
        [storage_application_observable_output.initial_writes_pubdata_queue_state];

    let repeated_writes_queues_states =
        [storage_application_observable_output.repeated_writes_pubdata_queue_state];

    let rollup_initital_writes_pubdata_hash = Bytes32::<E>::alloc_from_witness(
        cs,
        project_ref!(witness, rollup_initital_writes_pubdata_hash).cloned(),
    )?;
    let rollup_repeated_writes_pubdata_hash = Bytes32::<E>::alloc_from_witness(
        cs,
        project_ref!(witness, rollup_repeated_writes_pubdata_hash).cloned(),
    )?;

    let initial_writes_pubdata_hashes = [rollup_initital_writes_pubdata_hash];
    let repeated_writes_pubdata_hashes = [rollup_repeated_writes_pubdata_hash];
    let storage_intermediate_sorted_queue_state = [rollup_storage_sorter_intermediate_queue_state];

    assert_eq!(NUM_PROCESSABLE_SHARDS, 1); // no support of porter as of yet

    for shard_id in 0..NUM_PROCESSABLE_SHARDS {
        // storage acesses filter
        let (storage_filter_input_com, storage_filter_output_com) =
            compute_filter_circuit_commitment(
                cs,
                &storage_queues_state[shard_id],
                &storage_intermediate_sorted_queue_state[shard_id],
                &filtered_storage_queues_state[shard_id],
                round_function,
            )?;
        storage_filter_input_commitments[shard_id] = storage_filter_input_com;
        storage_filter_output_commitments[shard_id] = storage_filter_output_com;

        // storage applicator for rollup subtree (porter subtree is shut down globally currently)
        let (storage_applicator_input_com, storage_applicator_output_com) =
            compute_storage_applicator_circuit_commitment(
                cs,
                &filtered_storage_queues_state[shard_id],
                &initial_state_roots[shard_id],
                &initial_enumeration_counters[shard_id],
                &final_state_roots[shard_id],
                &final_enumeration_counters[shard_id],
                &repeated_writes_queues_states[shard_id],
                &initial_writes_queues_states[shard_id],
                shard_id as u8,
                round_function,
            )?;
        storage_applicator_input_commitments[shard_id] = storage_applicator_input_com;
        storage_applicator_output_commitments[shard_id] = storage_applicator_output_com;

        // storage pubdata hasher: for both repeated writes and
        let comm = compute_pubdata_hasher_circuit_commitment(
            cs,
            &repeated_writes_queues_states[shard_id],
            &repeated_writes_pubdata_hashes[shard_id],
            round_function,
        )?;
        repeated_pubdata_hasher_input_commitments[shard_id] = comm.0;
        repeated_pubdata_hasher_output_commitments[shard_id] = comm.1;

        let comm = compute_pubdata_hasher_circuit_commitment(
            cs,
            &initial_writes_queues_states[shard_id],
            &initial_writes_pubdata_hashes[shard_id],
            round_function,
        )?;
        initial_pubdata_hasher_input_commitments[shard_id] = comm.0;
        initial_pubdata_hasher_output_commitments[shard_id] = comm.1;
    }

    // now let's map it for convenience, and later on walk over it

    let input_commitments_as_map = HashMap::<CircuitType, Num<E>>::from_iter(
        [
            (CircuitType::VM, vm_observable_input_commitment),
            (
                CircuitType::DecommitmentsFilter,
                decommittments_sorter_circuit_input_commitment,
            ),
            (
                CircuitType::Decommiter,
                code_decommitter_circuit_input_commitment,
            ),
            (
                CircuitType::LogDemultiplexer,
                log_demux_circuit_input_commitment,
            ),
            (
                CircuitType::KeccakPrecompile,
                keccak_circuit_observable_input_commitment,
            ),
            (
                CircuitType::Sha256Precompile,
                sha256_circuit_observable_input_commitment,
            ),
            (
                CircuitType::EcrecoverPrecompile,
                ecrecover_circuit_observable_input_commitment,
            ),
            (
                CircuitType::RamValidation,
                ram_validation_circuit_input_commitment,
            ),
            (CircuitType::EventsRevertsFilter, events_filter_input_com),
            // (CircuitType::EventsMerkelization, events_merkelizer_input_com),
            (
                CircuitType::L1MessagesRevertsFilter,
                l1_messages_filter_input_com,
            ),
            (
                CircuitType::L1MessagesMerkelization,
                l1_messages_merkelizer_input_com,
            ),
            (
                CircuitType::StorageFilter,
                storage_filter_input_commitments[0],
            ),
            (
                CircuitType::StorageApplicator,
                storage_applicator_input_commitments[0],
            ),
            (
                CircuitType::StorageFreshWritesHasher,
                initial_pubdata_hasher_input_commitments[0],
            ),
            (
                CircuitType::StorageRepeatedWritesHasher,
                repeated_pubdata_hasher_input_commitments[0],
            ),
            (CircuitType::L1MessagesHasher, l1_messages_hasher_input_com),
        ]
        .into_iter(),
    );

    let output_commitments_as_map = HashMap::<CircuitType, Num<E>>::from_iter(
        [
            (CircuitType::VM, vm_observable_output_commitment),
            (
                CircuitType::DecommitmentsFilter,
                decommittments_sorter_observable_output_commitment,
            ),
            (
                CircuitType::Decommiter,
                code_decommitter_observable_output_commitment,
            ),
            (
                CircuitType::LogDemultiplexer,
                log_demuxer_observable_output_commitment,
            ),
            (
                CircuitType::KeccakPrecompile,
                keccak_circuit_observable_output_commitment,
            ),
            (
                CircuitType::Sha256Precompile,
                sha256_circuit_observable_output_commitment,
            ),
            (
                CircuitType::EcrecoverPrecompile,
                ecrecover_circuit_observable_output_commitment,
            ),
            (CircuitType::EventsRevertsFilter, events_filter_output_com),
            // (CircuitType::EventsMerkelization, events_merkelizer_output_com),
            (
                CircuitType::L1MessagesRevertsFilter,
                l1_messages_filter_output_com,
            ),
            (
                CircuitType::L1MessagesMerkelization,
                l1_messages_merkelizer_output_com,
            ),
            (
                CircuitType::StorageFilter,
                storage_filter_output_commitments[0],
            ),
            (
                CircuitType::StorageApplicator,
                storage_applicator_output_commitments[0],
            ),
            (
                CircuitType::StorageFreshWritesHasher,
                initial_pubdata_hasher_output_commitments[0],
            ),
            (
                CircuitType::StorageRepeatedWritesHasher,
                repeated_pubdata_hasher_output_commitments[0],
            ),
            (CircuitType::L1MessagesHasher, l1_messages_hasher_output_com),
        ]
        .into_iter(),
    );

    let sequence_of_circuit_types = [
        CircuitType::VM,
        CircuitType::DecommitmentsFilter,
        CircuitType::Decommiter,
        CircuitType::LogDemultiplexer,
        CircuitType::KeccakPrecompile,
        CircuitType::Sha256Precompile,
        CircuitType::EcrecoverPrecompile,
        CircuitType::RamValidation,
        CircuitType::StorageFilter,
        CircuitType::StorageApplicator,
        CircuitType::StorageFreshWritesHasher,
        CircuitType::StorageRepeatedWritesHasher,
        CircuitType::EventsRevertsFilter,
        CircuitType::L1MessagesRevertsFilter,
        CircuitType::L1MessagesHasher,
        CircuitType::L1MessagesMerkelization,
    ];

    for pair in sequence_of_circuit_types.windows(2) {
        assert_eq!((pair[0] as u8) + 1, pair[1] as u8);
    }

    assert_eq!(
        sequence_of_circuit_types.len(),
        execution_stage_bitmask.len()
    );

    let mut cur_circuit_type = UInt8::from_uint(CircuitType::VM as u8);
    let mut exec_flag = Boolean::constant(true);
    let mut prev_completion_flag = Boolean::constant(true);
    let mut prev_observable_input_commitment = Num::<E>::zero();
    let mut prev_hidden_fsm_output_commitment = Num::<E>::zero();

    let mut full_inputs_witnesses = project_ref!(witness, per_circuit_closed_form_inputs).cloned();

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    if let Some(inputs) = &full_inputs_witnesses {
        assert!(
            limit as usize >= inputs.len(),
            "The scheduler inputs limit is too small"
        );
    }

    for _idx in 0..limit {
        let closed_form_input_wit = if exec_flag.get_value().unwrap_or(false) {
            get_vec_witness_raw(
                &mut full_inputs_witnesses,
                ClosedFormInputCompactForm::<E>::placeholder_witness(),
            )
        } else {
            Some(ClosedFormInputCompactForm::<E>::placeholder_witness())
        };

        // wit_substitutor.get_next_witness(&exec_flag);
        let closed_form_input =
            ClosedFormInputCompactForm::<E>::alloc_from_witness(cs, closed_form_input_wit)?;
        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&closed_form_input.start_flag, E::Fr::one());
        lc.add_assign_boolean_with_coeff(&prev_completion_flag, minus_one);
        let tmp = lc.into_num(cs)?;

        let start_of_next_when_previous_is_finished = tmp.is_zero(cs)?;
        can_not_be_false_if_flagged(cs, &start_of_next_when_previous_is_finished, &exec_flag)?;

        let closed_form_input_comm = commit_encodable_item(cs, &closed_form_input, round_function)?;
        let proof_query = RecursiveProofQuery::<E> {
            cicruit_type: cur_circuit_type.clone(),
            closed_form_input_hash: closed_form_input_comm,
        };
        recursive_queue.push(cs, &proof_query, &exec_flag, round_function)?;

        let masked_start_flag = Boolean::and(cs, &exec_flag, &closed_form_input.start_flag)?;
        let masked_completion_flag =
            Boolean::and(cs, &exec_flag, &closed_form_input.completion_flag)?;

        for sample_circuit_type in sequence_of_circuit_types.iter() {
            let sample_circuit_commitment = input_commitments_as_map
                .get(sample_circuit_type)
                .cloned()
                .unwrap_or(Num::zero());
            validate_circuit_commitment(
                cs,
                &masked_start_flag,
                &cur_circuit_type,
                sample_circuit_type,
                &closed_form_input.observable_input_committment,
                &sample_circuit_commitment,
            )?;

            let sample_circuit_commitment = output_commitments_as_map
                .get(sample_circuit_type)
                .cloned()
                .unwrap_or(Num::zero());
            validate_circuit_commitment(
                cs,
                &masked_completion_flag,
                &cur_circuit_type,
                sample_circuit_type,
                &closed_form_input.observable_output_committment,
                &sample_circuit_commitment,
            )?;
        }

        // if not start flag : observable_input commitment should be the same as the previous one
        let should_enforce = smart_and(cs, &[masked_start_flag.not(), exec_flag])?;
        let comms_are_equal = Num::equals(
            cs,
            &closed_form_input.observable_input_committment,
            &prev_observable_input_commitment,
        )?;
        can_not_be_false_if_flagged(cs, &comms_are_equal, &should_enforce)?;

        // if not start flag : prev_hidden_fsm_output = cur_hidden_fsm_input
        let comms_are_equal = Num::equals(
            cs,
            &closed_form_input.hidden_fsm_input_committment,
            &prev_hidden_fsm_output_commitment,
        )?;
        can_not_be_false_if_flagged(cs, &comms_are_equal, &should_enforce)?;

        // increment curcuit type if needed, modify exec flag
        cur_circuit_type =
            cur_circuit_type.conditionally_increment_unchecked(cs, &masked_completion_flag)?;
        // let circuit_type_is_none = UInt8::equals(cs, &cur_circuit_type, &UInt8::from_uint(CircuitType::None as u8))?;
        let circuit_type_is_none = UInt8::equals(
            cs,
            &cur_circuit_type,
            &UInt8::from_uint(CircuitType::EventsMerkelization as u8),
        )?;
        exec_flag = circuit_type_is_none.not();

        prev_completion_flag = closed_form_input.completion_flag;
        prev_observable_input_commitment = closed_form_input.observable_input_committment.clone();
        prev_hidden_fsm_output_commitment = closed_form_input.hidden_fsm_output_committment;
    }

    dbg!(recursive_queue.tail_state.get_value());

    // Form a public block header
    let mut this_block_data = prev_block_data.clone();

    for ((dst, counter), root) in this_block_data
        .per_shard_states
        .iter_mut()
        .zip(final_enumeration_counters.iter())
        .zip(final_state_roots.iter())
    {
        dst.enumeration_counter = *counter;
        let mut root_bytes = vec![];
        let bytes = root[0].into_le_bytes(cs)?;
        root_bytes.extend(bytes);
        let bytes = root[1].into_le_bytes(cs)?;
        root_bytes.extend(bytes);
        dst.state_root.inner = root_bytes.try_into().unwrap();
    }

    let aux_data = BlockAuxilaryOutput {
        l1_messages_root: l1messages_merklizer_observable_output.root_hash,
        l1_messages_linear_hash: l1messages_linear_hasher_observable_output.pubdata_hash,
        rollup_initital_writes_pubdata_hash,
        rollup_repeated_writes_pubdata_hash,
    };

    let block_content_header = BlockContentHeader {
        block_data: this_block_data,
        block_meta: block_meta_parameters,
        auxilary_output: aux_data,
    };

    let (this_block_content_hash, (data_hash, meta_hash, aux_hash)) =
        block_content_header.clone().into_formal_block_hash(cs)?;

    // we are done with this block, process the previous one
    use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::Keccak256Gadget;
    let keccak_gadget = Keccak256Gadget::new(
        cs,
        None,
        None,
        None,
        None,
        true,
        RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME,
    )?;

    let previous_block_passthrough_data = prev_block_data.into_flattened_bytes(cs)?;
    let previous_block_passthrough_hash =
        keccak_gadget.digest_from_bytes(cs, &previous_block_passthrough_data)?;
    let previous_block_passthrough_hash =
        keccak_output_into_bytes(cs, previous_block_passthrough_hash)?;

    let previous_block_meta_hash = project_ref!(witness, previous_block_meta_hash).cloned();
    let previous_block_meta_hash = Bytes32::alloc_from_witness(cs, previous_block_meta_hash)?;

    let previous_block_aux_hash = project_ref!(witness, previous_block_aux_hash).cloned();
    let previous_block_aux_hash = Bytes32::alloc_from_witness(cs, previous_block_aux_hash)?;

    let previous_block_content_hash = BlockContentHeader::formal_block_hash_from_partial_hashes(
        cs,
        previous_block_passthrough_hash,
        previous_block_meta_hash.inner,
        previous_block_aux_hash.inner,
    )?;

    // It may be a generic queries hash in here, but we for now only have previous block hash

    // {
    //     let previous_content_hash_from_bootloader_heap = all_memory_queries[PREVIOUS_BLOCK_HASH_QUERY_KEY];
    //     let previous_content_hash_as_u256 = UInt256::from_be_bytes_fixed(cs, &previous_block_content_hash)?;
    //     for (a, b) in previous_content_hash_as_u256.inner.iter().zip(previous_content_hash_from_bootloader_heap.inner.iter()) {
    //         a.inner.enforce_equal(cs, &b.inner)?;
    //     }
    // }

    // form full block hash

    let mut flattened_public_input = vec![];
    flattened_public_input.extend(previous_block_content_hash);
    flattened_public_input.extend(this_block_content_hash);
    // recursion parameters

    let recursion_node_verification_key_hash =
        project_ref!(witness, recursion_node_verification_key_hash).cloned();
    let recursion_node_verification_key_hash =
        Bytes32::alloc_from_witness(cs, recursion_node_verification_key_hash)?;

    let recursion_leaf_verification_key_hash =
        project_ref!(witness, recursion_leaf_verification_key_hash).cloned();
    let recursion_leaf_verification_key_hash =
        Bytes32::alloc_from_witness(cs, recursion_leaf_verification_key_hash)?;

    let all_different_circuits_keys_hash =
        project_ref!(witness, all_different_circuits_keys_hash).cloned();
    let all_different_circuits_keys_hash =
        Bytes32::alloc_from_witness(cs, all_different_circuits_keys_hash)?;

    flattened_public_input.extend(recursion_node_verification_key_hash.inner);
    flattened_public_input.extend(recursion_leaf_verification_key_hash.inner);
    flattened_public_input.extend(all_different_circuits_keys_hash.inner);

    let recursion_queue_state = recursive_queue.into_state();

    dbg!(&recursion_queue_state.create_witness());

    let shifts = compute_shifts::<E::Fr>();

    // perform recursive verification of 1 proof for a node

    let mut lc = LinearCombination::zero();
    let mut shift = 0;
    for el in recursion_node_verification_key_hash.inner.iter().rev() {
        lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
        shift += 8;
    }
    let node_vk_committment = lc.into_num(cs)?;

    dbg!(node_vk_committment.get_value());

    let mut lc = LinearCombination::zero();
    let mut shift = 0;
    for el in recursion_leaf_verification_key_hash.inner.iter().rev() {
        lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
        shift += 8;
    }
    let leaf_vk_committment = lc.into_num(cs)?;

    dbg!(leaf_vk_committment.get_value());

    let mut lc = LinearCombination::zero();
    let mut shift = 0;
    for el in all_different_circuits_keys_hash.inner.iter().rev() {
        lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
        shift += 8;
    }
    let all_different_circuits_keys_committment = lc.into_num(cs)?;

    dbg!(all_different_circuits_keys_committment.get_value());

    let input_for_node = NodeAggregationInputData {
        node_vk_committment: node_vk_committment,
        leaf_vk_committment: leaf_vk_committment,
        all_circuit_types_committment_for_leaf: all_different_circuits_keys_committment,
        initial_log_queue_state: recursion_queue_state,
    };

    let aggregation_result = project_ref!(witness, aggregation_result).cloned();
    let aggregation_result = NodeAggregationOutputData::alloc_from_witness(cs, aggregation_result)?;

    let node_closed_form_input = NodeAggregationInputOutput {
        start_flag: Boolean::constant(true),
        completion_flag: Boolean::constant(true), // those do not matter
        observable_input: input_for_node,
        observable_output: aggregation_result.clone(),
        hidden_fsm_input: (),
        hidden_fsm_output: (),
        _marker_e: std::marker::PhantomData,
    };

    let node_closed_form_input_compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &node_closed_form_input, round_function)?;
    let node_closed_form_input_committment =
        commit_encodable_item(cs, &node_closed_form_input_compact_form, round_function)?;

    let vk_to_use = node_vk_committment;
    let input_to_use = node_closed_form_input_committment;

    let key_committments = vec![vk_to_use];
    let inputs = vec![input_to_use];
    let aggregation_results = vec![aggregation_result];

    assert_eq!(key_committments.len(), inputs.len());
    assert_eq!(key_committments.len(), 1);

    use crate::recursion::node_aggregation::aggregate_generic_inner;

    let aggregation_proofs = project_ref!(witness, proof_witnesses).cloned();

    let vks_raw_elements_witness = project_ref!(witness, vk_encoding_witnesses).map(|el| {
        let mut result = vec![];
        for subset in el.iter().cloned() {
            let r = subset.try_into().unwrap();
            result.push(r);
        }

        result
    });

    // do actual work
    let [[pair_with_generator_x, pair_with_generator_y], [pair_with_x_x, pair_with_x_y]] =
        aggregate_generic_inner::<_, _, _, _, _, _, true>(
            cs,
            key_committments,
            inputs,
            aggregation_proofs,
            aggregation_params,
            &rns_params,
            padding_proof,
            Some(aggregation_results),
            round_function,
            vks_raw_elements_witness,
            padding_vk_encoding,
            g2_elements,
            1,
        )?;

    let mut coordinates_bytes_witness: Vec<[u8; 32]> = vec![];

    for coord in [
        pair_with_generator_x,
        pair_with_generator_y,
        pair_with_x_x,
        pair_with_x_y,
    ]
    .into_iter()
    {
        let mut bytes_left = 32;
        let take_by = 10; // 80 bits
        let mut le_bytes: Vec<Byte<E>> = vec![];
        for el in coord.into_iter() {
            let as_u256 = UInt256::canonical_from_num(cs, &el)?;
            let as_le_bytes = as_u256.into_le_bytes_strict(cs)?;
            if bytes_left >= take_by {
                le_bytes.extend_from_slice(&as_le_bytes[..take_by]);
                bytes_left -= take_by;
            } else {
                le_bytes.extend_from_slice(&as_le_bytes[..bytes_left]);
                break;
            }
        }

        assert_eq!(le_bytes.len(), 32);

        le_bytes.reverse();

        let mut byte_witness = vec![];
        let mut have_witness = true;
        for el in le_bytes.iter() {
            if let Some(v) = el.get_byte_value() {
                byte_witness.push(v);
            } else {
                have_witness = false;
                break;
            }
        }

        if have_witness {
            coordinates_bytes_witness.push(byte_witness.try_into().unwrap());
        }

        flattened_public_input.extend(le_bytes);
    }

    let digest = keccak_gadget.digest_from_bytes(cs, &flattened_public_input)?;
    let input_keccak_hash = keccak_output_into_bytes(cs, digest)?;

    let mut lc = LinearCombination::zero();
    let to_take = (E::Fr::CAPACITY as usize) / 8;
    let mut shift = 0;

    for el in input_keccak_hash.iter().rev().take(to_take) {
        lc.add_assign_number_with_coeff(&el.inner, shifts[shift]);
        shift += 8;
    }
    assert!(shift <= E::Fr::CAPACITY as usize);

    let input = lc.into_num(cs)?;
    let input_value = input.get_value();
    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_value.grab()?))?;
    public_input.enforce_equal(cs, &input.get_variable())?;

    if crate::VERBOSE_CIRCUITS {
        match (
            Byte::get_byte_value_multiple(&input_keccak_hash),
            block_content_header.create_witness(),
            Byte::get_byte_value_multiple(&this_block_content_hash),
            Byte::get_byte_value_multiple(&data_hash),
            Byte::get_byte_value_multiple(&meta_hash),
            Byte::get_byte_value_multiple(&aux_hash),
        ) {
            (
                Some(input_keccak_hash),
                Some(content_header),
                Some(block_hash),
                Some(data_hash),
                Some(meta_hash),
                Some(aux_hash),
            ) => {
                println!("Input keccak hash = 0x{}", hex::encode(&input_keccak_hash));
                println!("Content header = {:?}", content_header);
                println!("Block hash = {:?}", hex::encode(&block_hash));
                println!("Data hash = {:?}", hex::encode(&data_hash));
                println!("Meta hash = {:?}", hex::encode(&meta_hash));
                println!("Aux hash = {:?}", hex::encode(&aux_hash));
            }
            _ => {}
        }
    }

    if let Some(reporting_function) = reporting_function {
        let coordinates_bytes_witness: [[u8; 32]; 4] =
            coordinates_bytes_witness.try_into().unwrap();

        match (
            Byte::get_byte_value_multiple(&input_keccak_hash),
            block_content_header.create_witness(),
            Byte::get_byte_value_multiple(&this_block_content_hash),
            Byte::get_byte_value_multiple(&data_hash),
            Byte::get_byte_value_multiple(&meta_hash),
            Byte::get_byte_value_multiple(&aux_hash),
        ) {
            (
                Some(input_keccak_hash),
                Some(content_header),
                Some(block_hash),
                Some(data_hash),
                Some(meta_hash),
                Some(aux_hash),
            ) => {
                let report = BlockApplicationWitness {
                    passthrough_data_part: content_header.block_data,
                    passthrough_data_hash: data_hash,
                    aux_data_part: content_header.auxilary_output,
                    aux_data_hash: aux_hash,
                    meta_data_part: content_header.block_meta,
                    meta_data_hash: meta_hash,
                    block_header_hash: block_hash,
                    aggregation_result_coords: coordinates_bytes_witness,
                    committment_bytes: input_keccak_hash,
                };

                reporting_function(report);
            }
            _ => {}
        }
    }

    Ok(public_input)
}
