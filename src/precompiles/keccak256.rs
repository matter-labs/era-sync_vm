use super::*;

use crate::circuit_structures::traits::*;
use crate::franklin_crypto::plonk::circuit::byte::*;
use crate::franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::*;
use crate::glue::aux_byte_markers::*;
use crate::glue::optimizable_queue::*;
use crate::glue::traits::get_vec_vec_witness_raw_with_hint_on_more_in_subset;
use crate::traits::*;
use crate::utils::fe_to_u64;
use crate::vm::optimizer::sponge_set::SpongeOptimizer;
use crate::vm::primitives::uint256::*;
use crate::vm::primitives::*;
use num_bigint::BigUint;
use num_integer::Integer;

use crate::vm::structural_eq::*;
use cs_derive::*;

use crate::glue::code_unpacker_sha256::memory_query_updated::{
    MemoryQueriesQueue, MemoryQuery, MemoryQueryWitness, RawMemoryQuery,
};

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct KeccakPrecompileState<E: Engine> {
    pub read_precompile_call: Boolean,
    pub read_unaligned_words_for_round: Boolean,
    pub completed: Boolean,
    pub keccak_internal_state: [Num<E>; 25],
    pub timestamp_to_use_for_read: UInt32<E>,
    pub timestamp_to_use_for_write: UInt32<E>,
    pub call_params: KeccakPrecompileCallParams<E>,
    pub u64_words_buffer: [UInt64<E>; BUFFER_SIZE],
    pub u64_words_buffer_markers: [Boolean; BUFFER_SIZE],
}

impl<E: Engine> KeccakPrecompileState<E> {
    pub fn empty() -> Self {
        Self {
            read_precompile_call: Boolean::constant(false),
            read_unaligned_words_for_round: Boolean::constant(false),
            completed: Boolean::constant(false),
            keccak_internal_state: [Num::<E>::zero(); 25],
            timestamp_to_use_for_read: UInt32::<E>::zero(),
            timestamp_to_use_for_write: UInt32::<E>::zero(),
            call_params: KeccakPrecompileCallParams::<E>::empty(),
            u64_words_buffer: [UInt64::<E>::zero(); BUFFER_SIZE],
            u64_words_buffer_markers: [Boolean::constant(false); BUFFER_SIZE],
        }
    }
}

pub const READ_CALL_INFO_ID: u64 = 0;
pub const READ_U256_WORD_AND_USE_BUFFER: u64 = 1;
pub const READ_U64_FROM_BUFFER: u64 = 2;

pub const KECCAK256_PRECOMPILE_ADDRESS: u64 = 0x8010;

pub const KECCAK_RATE_IN_U64_WORDS: usize = 17;
pub const MEMORY_EQURIES_PER_CYCLE: usize = 5; // we need to read as much as possible to use a round function every cycle
pub const NEW_WORDS_PER_CYCLE: usize = 4 * MEMORY_EQURIES_PER_CYCLE;
// we absorb 17 elements per cycle, and add 20 elements per cycle, so we need to skip memory reads
// sometimes and do absorbs instead
pub const BUFFER_SIZE: usize = NEW_WORDS_PER_CYCLE + KECCAK_RATE_IN_U64_WORDS - 1;

// Binary interface of this precompile is:
// - 1st 32byte word contains UInt16 (upper bits are ignored) that encodes a total number of Keccak256 ROUNDS
// Let's denote it as NUM_ROUNDS
// - words[1..(1 + ceil(NUM_ROUNDS * 17 / 4))] contain PADDED and ALIGNED input data. Each keccak256 round absorbs
// 17 64bit words (we also need to change endianess), and we can fit 4 words into 32 bytes of memory slot

use crate::scheduler::queues::StorageLogQueue;
use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::{
    Keccak256Gadget, KeccakState,
};

use sha3::Digest;

type Keccak256InnerState = [u64; 25];

#[derive(Debug)]
struct BlockBuffer {
    _buffer: [u8; 136],
    _pos: u8,
}

#[derive(Debug)]
struct CoreWrapper {
    core: Keccak256VarCore,
    _buffer: BlockBuffer,
}

#[derive(Debug)]
struct Keccak256VarCore {
    state: Keccak256InnerState,
}

fn transmute_state(reference_state: sha3::Keccak256) -> Keccak256InnerState {
    // we use a trick that size of both structures is the same, and even though we do not know a stable field layout,
    // we can replicate it
    let our_wrapper: CoreWrapper = unsafe { std::mem::transmute(reference_state) };

    our_wrapper.core.state
}

pub struct KeccakSelfVerifier {
    internal_state: sha3::Keccak256,
    buffer: zk_evm::precompiles::keccak256::Buffer,
}

impl KeccakSelfVerifier {
    pub fn new() -> Self {
        Self {
            internal_state: sha3::Keccak256::new(),
            buffer: zk_evm::precompiles::keccak256::Buffer::new(),
        }
    }
    pub fn reset(&mut self) {
        self.internal_state = sha3::Keccak256::new();
        self.buffer.reset();
    }
    pub fn add_to_buffer<E: Engine>(
        &mut self,
        values: &[UInt64<E>; NEW_WORDS_PER_CYCLE],
    ) -> Option<()> {
        assert!(self.buffer.can_read_into());
        assert!(
            self.buffer.filled <= BUFFER_SIZE - NEW_WORDS_PER_CYCLE,
            "have {} words filled, but the limit is {}",
            self.buffer.filled,
            BUFFER_SIZE - NEW_WORDS_PER_CYCLE
        );
        let mut tmp = Vec::with_capacity(NEW_WORDS_PER_CYCLE);
        for el in values.iter() {
            let value = el.get_value()?;
            tmp.push(value);
        }

        let tmp = tmp.try_into().unwrap();
        self.buffer.append(&tmp);

        None
    }
    pub fn pretend_buffer_is_filled(&mut self) {
        self.buffer.filled = KECCAK_RATE_IN_U64_WORDS;
    }
    pub fn run_round_function(&mut self, cycle_idx: usize) -> [u64; 25] {
        assert!(
            self.buffer.filled >= KECCAK_RATE_IN_U64_WORDS,
            "failed at cycle {}",
            cycle_idx
        );
        let to_append = self.buffer.consume_rate();
        let mut tmp = Vec::with_capacity(8 * to_append.len());
        for el in to_append.into_iter() {
            tmp.extend(el.to_le_bytes());
        }
        self.internal_state.update(&tmp);
        let internal_state_raw =
            zk_evm::precompiles::keccak256::transmute_state(self.internal_state.clone());

        internal_state_raw
    }
    pub fn compare_states<E: Engine>(
        raw_state: [u64; 25],
        circuit_state: &[Num<E>; 25],
        cycle_idx: usize,
    ) -> Option<()> {
        // note the transposition
        for row in 0..5 {
            for column in 0..5 {
                let expected = raw_state[5 * row + column];
                let circuit = circuit_state[5 * column + row];
                let circuit = circuit.get_value()?;
                let as_u64 = fe_to_u64(circuit);
                assert_eq!(
                    expected, as_u64,
                    "diverged at cycle idx {}, element at row {}, column {}",
                    cycle_idx, row, column
                );
            }
        }

        None
    }
    pub fn set_internal_state<E: Engine>(&mut self, circuit_state: &[Num<E>; 25]) -> Option<()> {
        // note the transposition
        let cast_ref = unsafe { &mut *(&mut self.internal_state as *mut _ as *mut CoreWrapper) };
        for row in 0..5 {
            for column in 0..5 {
                let expected = &mut cast_ref.core.state[5 * row + column];
                let circuit = circuit_state[5 * column + row];
                let circuit = circuit.get_value()?;
                let as_u64 = fe_to_u64(circuit);
                *expected = as_u64;
            }
        }

        None
    }
    pub fn set_buffer_state<E: Engine>(
        &mut self,
        circuit_state_els: &[UInt64<E>; BUFFER_SIZE],
        circuit_state_markers: &[Boolean; BUFFER_SIZE],
    ) -> Option<()> {
        // NOTE: we always run FULL rounds of Keccak, so we do not care about internal buffer of
        // out of circuit implementation

        // also work with buffer
        for (value, marker) in circuit_state_els.iter().zip(circuit_state_markers.iter()) {
            if marker.get_value().unwrap_or(false) {
                self.buffer.words[self.buffer.filled] = value.get_value()?;
                self.buffer.filled += 1;
            } else {
                break;
            }

            assert!(self.buffer.filled <= BUFFER_SIZE);
        }

        assert!(self.buffer.filled <= BUFFER_SIZE);

        None
    }
}

pub fn keccak256_precompile_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    memory_queue: &mut MemoryQueriesQueue<E, 2, 3>,
    precompile_calls_queue: &mut StorageLogQueue<E>,
    mut input_witness: Option<Vec<Vec<BigUint>>>,
    state: KeccakPrecompileState<E>,
    round_function: &R,
    limit: usize,
) -> Result<KeccakPrecompileState<E>, SynthesisError> {
    let mut state = state;
    assert!(limit <= u32::MAX as usize);

    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    let precompile_address = UInt160::<E>::from_uint(u160::from_u64(KECCAK256_PRECOMPILE_ADDRESS));
    let aux_byte_for_precompile = aux_byte_for_precompile_call::<E>();

    let keccak_gadget = Keccak256Gadget::new(
        cs,
        None,
        None,
        None,
        None,
        true,
        RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME,
    )?;

    let mut self_checker = KeccakSelfVerifier::new();
    if state.read_precompile_call.get_value().unwrap_or(false) == false {
        // set internal state
        let _ = self_checker.set_internal_state(&state.keccak_internal_state);
        // and buffer
        let _ =
            self_checker.set_buffer_state(&state.u64_words_buffer, &state.u64_words_buffer_markers);
    }

    // we can have a degenerate case when queue is empty, but it's a first circuit in the queue,
    // so we taken default FSM state that has state.read_precompile_call = true;
    let is_empty = precompile_calls_queue.is_empty(cs)?;
    state.read_precompile_call = smart_and(cs, &[state.read_precompile_call, is_empty.not()])?;
    state.completed = smart_or(cs, &[state.completed, is_empty])?;

    for _cycle in 0..limit {
        // if we are in a proper state then get the ABI from the queue
        let precompile_call =
            precompile_calls_queue.pop_first(cs, &state.read_precompile_call, round_function)?;

        let aux_byte_is_valid = Num::equals(
            cs,
            &precompile_call.aux_byte.inner,
            &aux_byte_for_precompile.inner,
        )?;

        let precompile_address_is_valid = Num::equals(
            cs,
            &precompile_call.address.inner,
            &precompile_address.inner,
        )?;

        let call_is_valid = smart_and(cs, &[aux_byte_is_valid, precompile_address_is_valid])?;
        can_not_be_false_if_flagged(cs, &call_is_valid, &state.read_precompile_call)?;

        // now compute some parameters that describe the call itself

        let params_encoding = precompile_call.key;
        let call_params = KeccakPrecompileCallParams::from_encoding(cs, params_encoding)?;

        state.call_params = KeccakPrecompileCallParams::conditionally_select(
            cs,
            &state.read_precompile_call,
            &call_params,
            &state.call_params,
        )?;

        // also set timestamps
        state.timestamp_to_use_for_read = UInt32::conditionally_select(
            cs,
            &state.read_precompile_call,
            &precompile_call.timestamp,
            &state.timestamp_to_use_for_read,
        )?;
        let (timestamp_to_use_for_write, of) =
            state.timestamp_to_use_for_read.increment_checked(cs)?;
        Boolean::enforce_equal(cs, &of, &Boolean::constant(false))?;
        state.timestamp_to_use_for_write = UInt32::conditionally_select(
            cs,
            &state.read_precompile_call,
            &timestamp_to_use_for_write,
            &state.timestamp_to_use_for_write,
        )?;

        // and do some work! keccak256 is expensive
        let reset_buffer = smart_or(cs, &[state.read_precompile_call, state.completed])?;
        state.read_unaligned_words_for_round = smart_or(
            cs,
            &[
                state.read_precompile_call,
                state.read_unaligned_words_for_round,
            ],
        )?;
        state.read_precompile_call = Boolean::constant(false);

        if reset_buffer.get_value().unwrap_or(false) {
            self_checker.reset();
        }

        // ---------------------------------
        // Now perform few memory queries to read content

        for el in state.u64_words_buffer_markers.iter_mut() {
            *el = Boolean::conditionally_select(cs, &reset_buffer, &Boolean::constant(false), el)?;
        }

        // even though it's not important, we cleanup the buffer too
        for el in state.u64_words_buffer.iter_mut() {
            *el = UInt64::conditionally_select(cs, &reset_buffer, &UInt64::zero(), el)?;
        }

        let initial_buffer_len = {
            let mut lc = LinearCombination::zero();
            for is_busy in state.u64_words_buffer_markers.iter() {
                lc.add_assign_boolean_with_coeff(is_busy, E::Fr::one());
            }
            let num = lc.into_num(cs)?;

            UInt16::from_num_unchecked(num)
        };

        // we can fill the buffer as soon as it's length <= MAX - NEW_WORDS_PER_CYCLE
        let (_, of) = initial_buffer_len.sub(
            cs,
            &UInt16::from_uint((BUFFER_SIZE - NEW_WORDS_PER_CYCLE + 1) as u16),
        )?;
        let can_fill = of;
        let zero_rounds_left = state.call_params.num_rounds.is_zero(cs)?;
        // we have a condition that if buffer is full then we can not be in the state that

        // if we can not fill then we should (sanity check) be in a state of reading new words
        // and have >0 rounds left
        can_not_be_false_if_flagged(cs, &state.read_unaligned_words_for_round, &can_fill.not())?;
        can_not_be_false_if_flagged(cs, &zero_rounds_left.not(), &can_fill.not())?;

        let mut memory_queries_as_u64_words = vec![];
        let should_read = smart_and(
            cs,
            &[
                zero_rounds_left.not(),
                state.read_unaligned_words_for_round,
                can_fill,
            ],
        )?;
        for _i in 0..MEMORY_EQURIES_PER_CYCLE {
            let memory_query_witness = if let Some(should_read) = should_read.get_value() {
                if should_read {
                    let (wit, _) = get_vec_vec_witness_raw_with_hint_on_more_in_subset(
                        &mut input_witness,
                        BigUint::from(0u64),
                    );

                    wit
                } else {
                    Some(BigUint::from(0u64))
                }
            } else {
                None
            };
            let (u256_value, le_bytes) =
                UInt256::alloc_from_biguint_and_return_u8_chunks(cs, memory_query_witness)?;
            let mut memory_query = MemoryQuery::<E>::empty();
            memory_query.timestamp = state.timestamp_to_use_for_read;
            memory_query.memory_page = state.call_params.input_page;
            memory_query.memory_index = state.call_params.input_offset;
            memory_query.rw_flag = Boolean::constant(false);
            memory_query.value = u256_value;

            state.call_params.input_offset = state
                .call_params
                .input_offset
                .conditionally_increment_unchecked(cs, &should_read)?;
            let raw_query = memory_query.into_raw_query(cs)?;
            // perform read
            memory_queue.push(cs, &raw_query, &should_read, round_function)?;

            // proper order of words, and of bytes
            let mut be_bytes = le_bytes;
            be_bytes.reverse();
            for chunk in be_bytes.chunks(8) {
                let chunk: [Byte<E>; 8] = chunk
                    .iter()
                    .map(|el| Byte::from_num_unconstrained(cs, *el))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let le_integer = UInt64::from_bytes_le(cs, &chunk)?;
                memory_queries_as_u64_words.push(le_integer);
            }
        }

        let new_elements: [UInt64<E>; NEW_WORDS_PER_CYCLE] =
            memory_queries_as_u64_words.try_into().unwrap();

        if should_read.get_value().unwrap_or(false) {
            self_checker.add_to_buffer(&new_elements);
        } else {
            if state.completed.get_value().unwrap_or(false) {
                self_checker.pretend_buffer_is_filled();
            }
        }

        // our buffer len fits at least to push new elements and get enough for round function
        // this is quadratic complexity, but we it's easier to handle and cheap compared to round function
        let should_push = should_read;

        for src in new_elements.into_iter() {
            let mut should_push = should_push;
            for (is_busy, dst) in state
                .u64_words_buffer_markers
                .iter_mut()
                .zip(state.u64_words_buffer.iter_mut())
            {
                let update = smart_and(cs, &[is_busy.not(), should_push])?;
                *dst = UInt64::conditionally_select(cs, &update, &src, &dst)?;
                *is_busy = smart_or(cs, &[update, *is_busy])?;
                should_push = smart_and(cs, &[should_push, update.not()])?;
            }

            Boolean::enforce_equal(cs, &should_push, &Boolean::constant(false))?;
        }

        state.call_params.num_rounds = state
            .call_params
            .num_rounds
            .conditionally_decrement_unchecked(cs, &state.read_unaligned_words_for_round)?;
        // absorb

        // compute shifted buffer that removes first RATE elements and padds with something

        let input: [_; KECCAK_RATE_IN_U64_WORDS] = state.u64_words_buffer
            [..KECCAK_RATE_IN_U64_WORDS]
            .iter()
            .map(|el| el.inner)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // for (i, el) in input.iter().enumerate() {
        //     println!("Input u64 word {} = {}", i, el.get_value().unwrap());
        // }

        // we make it in such a way that we ALWAYS absorb every round (since we try to fill as much as we can),
        // so we can just take subslice
        let mut tmp_buffer = state.u64_words_buffer[KECCAK_RATE_IN_U64_WORDS..].to_vec();
        tmp_buffer.resize(BUFFER_SIZE, UInt64::zero());
        let tmp_buffer: [UInt64<E>; BUFFER_SIZE] = tmp_buffer.try_into().unwrap();
        state.u64_words_buffer = tmp_buffer;

        let mut tmp_buffer_markers =
            state.u64_words_buffer_markers[KECCAK_RATE_IN_U64_WORDS..].to_vec();
        tmp_buffer_markers.resize(BUFFER_SIZE, Boolean::constant(false));
        let tmp_buffer_markers: [Boolean; BUFFER_SIZE] = tmp_buffer_markers.try_into().unwrap();
        state.u64_words_buffer_markers = tmp_buffer_markers;

        let current_keccak_state = <[Num<E>; 25]>::conditionally_select(
            cs,
            &reset_buffer,
            &[Num::<E>::zero(); 25],
            &state.keccak_internal_state,
        )?;

        let mut current_keccak_state = KeccakState::from_raw(current_keccak_state);
        current_keccak_state.base = KeccakStateBase::Binary;

        let state_after_absorb = keccak_gadget.keccak_absorb_into_state_into_binary_base(
            cs,
            current_keccak_state,
            input,
        )?;
        assert!(state_after_absorb.base == KeccakStateBase::First);
        let (new_inner, squeezed) = keccak_gadget
            .keccak_normal_rounds_function_state_in_first_base(cs, state_after_absorb)?;
        assert!(new_inner.base == KeccakStateBase::Binary);

        // prevent running it in setup generation
        // to prevent asserts
        let raw_state = if state.read_unaligned_words_for_round.get_value().is_some() {
            self_checker.run_round_function(_cycle)
        } else {
            [0u64; 25]
        };

        state.keccak_internal_state = new_inner.into_raw();

        KeccakSelfVerifier::compare_states(raw_state, &state.keccak_internal_state, _cycle);

        let no_rounds_left = state.call_params.num_rounds.is_zero(cs)?;
        let write_result = smart_and(cs, &[state.read_unaligned_words_for_round, no_rounds_left])?;

        let mut result = UInt256::zero();
        assert_eq!(squeezed.len(), 4);
        // we have to again work with endianess
        let bytes0 = UInt64::from_num_unchecked(squeezed[0]).into_be_bytes(cs)?;
        let el0 = UInt64::from_bytes_le(cs, &bytes0.try_into().unwrap())?;
        let bytes1 = UInt64::from_num_unchecked(squeezed[1]).into_be_bytes(cs)?;
        let el1 = UInt64::from_bytes_le(cs, &bytes1.try_into().unwrap())?;
        let bytes2 = UInt64::from_num_unchecked(squeezed[2]).into_be_bytes(cs)?;
        let el2 = UInt64::from_bytes_le(cs, &bytes2.try_into().unwrap())?;
        let bytes3 = UInt64::from_num_unchecked(squeezed[3]).into_be_bytes(cs)?;
        let el3 = UInt64::from_bytes_le(cs, &bytes3.try_into().unwrap())?;

        result.inner[3] = el0;
        result.inner[2] = el1;
        result.inner[1] = el2;
        result.inner[0] = el3;

        let mut write_query = MemoryQuery::empty();
        write_query.timestamp = state.timestamp_to_use_for_write;
        write_query.memory_page = state.call_params.output_page;
        write_query.memory_index = state.call_params.output_offset;
        write_query.rw_flag = Boolean::constant(true);
        write_query.value = result;
        let raw_query = write_query.into_raw_query(cs)?;
        // perform write
        memory_queue.push(cs, &raw_query, &write_result, round_function)?;

        // ---------------------------------

        // update call props
        let input_is_empty = precompile_calls_queue.is_empty(cs)?;
        let nothing_left = smart_and(cs, &[write_result, input_is_empty])?;
        let process_next = smart_and(cs, &[write_result, input_is_empty.not()])?;

        state.read_precompile_call = process_next;
        state.completed = smart_or(cs, &[nothing_left, state.completed])?;
        state.read_unaligned_words_for_round =
            smart_or(cs, &[state.read_precompile_call, state.completed])?.not();
    }

    Ok(state)
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct KeccakPrecompileCallParams<E: Engine> {
    pub input_page: UInt32<E>,
    pub input_offset: UInt32<E>,
    pub output_page: UInt32<E>,
    pub output_offset: UInt32<E>,
    pub num_rounds: UInt16<E>,
}

impl<E: Engine> KeccakPrecompileCallParams<E> {
    pub fn empty() -> Self {
        Self {
            input_page: UInt32::<E>::zero(),
            input_offset: UInt32::<E>::zero(),
            output_page: UInt32::<E>::zero(),
            output_offset: UInt32::<E>::zero(),
            num_rounds: UInt16::<E>::zero(),
        }
    }

    pub fn from_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        encoding: UInt256<E>,
    ) -> Result<Self, SynthesisError> {
        let input_encoding = encoding.inner[0];
        let output_encoding = encoding.inner[1];
        let pages_encoding = encoding.inner[2];

        let shifts = compute_shifts::<E::Fr>();
        let input_chunks = input_encoding.decompose_into_uint16_in_place(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&input_chunks[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&input_chunks[1].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let input_offset = UInt32::from_num_unchecked(num);

        // not used in practice, as number of rounds is enough

        // let mut lc = LinearCombination::zero();
        // lc.add_assign_number_with_coeff(&input_chunks[2].inner, shifts[0]);
        // lc.add_assign_number_with_coeff(&input_chunks[3].inner, shifts[16]);
        // let num = lc.into_num(cs)?;
        // let input_length = UInt32::from_num_unchecked(num);

        let output_chunks = output_encoding.decompose_into_uint16_in_place(cs)?;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&output_chunks[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&output_chunks[1].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let output_offset = UInt32::from_num_unchecked(num);

        // let mut lc = LinearCombination::zero();
        // lc.add_assign_number_with_coeff(&output_chunks[2].inner, shifts[0]);
        // lc.add_assign_number_with_coeff(&output_chunks[3].inner, shifts[16]);
        // let num = lc.into_num(cs)?;
        // let output_length = UInt32::from_num_unchecked(num);

        let page_chunks = pages_encoding.decompose_into_uint16_in_place(cs)?;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&page_chunks[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&page_chunks[1].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let input_page = UInt32::from_num_unchecked(num);

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&page_chunks[2].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&page_chunks[3].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let output_page = UInt32::from_num_unchecked(num);

        let num_rounds = encoding.inner[3].decompose_into_uint16_in_place(cs)?[0];

        let new = Self {
            input_page,
            input_offset,
            output_page,
            output_offset,
            num_rounds,
        };

        Ok(new)
    }
}

fn unchecked_accumulate_byte_to_u64_word_be<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    dst: &mut UInt64<E>,
    byte: Byte<E>,
    execute: &Boolean,
) -> Result<(), SynthesisError> {
    // if we execute then dst = 2^8 * dst + byte, so
    let mut lc = LinearCombination::zero();
    let shift = E::Fr::from_str("256").unwrap();
    lc.add_assign_number_with_coeff(&dst.inner, shift);
    lc.add_assign_number_with_coeff(&byte.inner, E::Fr::one());
    let num = lc.into_num(cs)?;
    let tmp = UInt64::from_num_unchecked(num);

    *dst = UInt64::conditionally_select(cs, execute, &tmp, &*dst)?;

    Ok(())
}

pub fn u32_div_by_constant<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: UInt32<E>,
    constant: u32,
) -> Result<(UInt32<E>, UInt32<E>), SynthesisError> {
    assert!(constant != 1);
    let (q, r) = if let Some(value) = value.get_value() {
        let (q, r) = value.div_rem(&constant);

        (Some(q), Some(r))
    } else {
        (None, None)
    };
    let q = UInt32::alloc_from_witness(cs, q)?;
    let r = UInt32::alloc_from_witness(cs, r)?;
    // check that r < constant, two different cases
    if constant.is_power_of_two() {
        let mut tmp_shift = E::Fr::one();
        for _ in 0..(32 - constant.trailing_zeros()) {
            tmp_shift.double();
        }
        let r_shifted_raw = r.inner.mul(cs, &Num::Constant(tmp_shift))?;
        let _ = UInt32::from_num_checked(cs, &r_shifted_raw)?;
    } else {
        // subtract and check for borrow
        let (_, uf) = UInt32::from_uint(constant).sub(cs, &value)?;
        Boolean::enforce_equal(cs, &uf, &Boolean::constant(true))?;
    }

    // constraint the relation value = q * constant + r
    let mut lc = LinearCombination::zero();
    let shift = E::Fr::from_str(&constant.to_string()).unwrap();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    lc.add_assign_number_with_coeff(&q.inner, shift);
    lc.add_assign_number_with_coeff(&r.inner, E::Fr::one());
    lc.add_assign_number_with_coeff(&value.inner, minus_one);
    lc.enforce_zero(cs)?;

    Ok((q, r))
}

pub fn u16_div_by_constant<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: UInt16<E>,
    constant: u16,
) -> Result<(UInt16<E>, UInt16<E>), SynthesisError> {
    assert!(constant != 1);
    let (q, r) = if let Some(value) = value.get_value() {
        let (q, r) = value.div_rem(&constant);

        (Some(q), Some(r))
    } else {
        (None, None)
    };
    let q = UInt16::alloc_from_witness(cs, q)?;
    let r = UInt16::alloc_from_witness(cs, r)?;
    // check that r < constant, two different cases
    if constant.is_power_of_two() {
        let mut tmp_shift = E::Fr::one();
        for _ in 0..(16 - constant.trailing_zeros()) {
            tmp_shift.double();
        }
        let r_shifted_raw = r.inner.mul(cs, &Num::Constant(tmp_shift))?;
        let _ = UInt16::from_num_checked(cs, &r_shifted_raw)?;
    } else {
        // subtract and check for borrow
        let (_, uf) = UInt16::from_uint(constant).sub(cs, &value)?;
        Boolean::enforce_equal(cs, &uf, &Boolean::constant(true))?;
    }

    // constraint the relation value = q * constant + r
    let mut lc = LinearCombination::zero();
    let shift = E::Fr::from_str(&constant.to_string()).unwrap();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    lc.add_assign_number_with_coeff(&q.inner, shift);
    lc.add_assign_number_with_coeff(&r.inner, E::Fr::one());
    lc.add_assign_number_with_coeff(&value.inner, minus_one);
    lc.enforce_zero(cs)?;

    Ok((q, r))
}

fn u4_constraint_bit_len<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    values: [Num<E>; 2],
) -> Result<(), SynthesisError> {
    use crate::precompiles::aux_tables::XOR_4_BIT_TABLE_NAME;
    use crate::precompiles::utils::table_width_3_lookup;

    let _ = table_width_3_lookup(cs, XOR_4_BIT_TABLE_NAME, &values)?;

    Ok(())
}

fn split_byte_as_u4x2_unchecked<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    byte: Byte<E>,
) -> Result<(Num<E>, Num<E>), SynthesisError> {
    let (low, high) = if let Some(value) = byte.get_byte_value() {
        let low = value & ((1u8 << 4) - 1);
        let high = value >> 4;

        let low = u64_to_fe(low as u64);
        let high = u64_to_fe(high as u64);

        (Some(low), Some(high))
    } else {
        (None, None)
    };

    let low = Num::alloc(cs, low)?;
    let high = Num::alloc(cs, high)?;

    Ok((low, high))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::testing::*;

    type E = Bn256;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    fn apply_keccak256_padding(input: &[u8]) -> Vec<u8> {
        let align_bytes = num_integer::Integer::next_multiple_of(&input.len(), &136);
        let mut result = Vec::with_capacity(align_bytes);
        result.extend_from_slice(input);
        let input_len = input.len();
        let mut padlen = align_bytes - input_len;
        if padlen == 0 {
            // another full block
            result.extend(std::iter::repeat(0x00).take(136));
        } else if padlen == 1 {
            result.push(0x81);
        } else {
            result.push(0x01);
            result.extend(std::iter::repeat(0x00).take(padlen - 2));
            result.push(0x80);
        }

        assert!(result.len() % 136 == 0);

        result
    }

    #[test]
    fn test_hash_one() -> Result<(), SynthesisError> {
        let (mut dummy_cs, committer, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;
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

        let mut rng = deterministic_rng();
        let mut input_length = 64;
        let num_rounds = 1;
        let mut input_bytes = vec![];
        for _ in 0..input_length {
            input_bytes.push(rng.gen::<u8>());
        }

        println!("Input = {}", hex::encode(&input_bytes));

        let padded_bytes = apply_keccak256_padding(&input_bytes);
        println!("Padded input = {}", hex::encode(&padded_bytes));
        // manual padding for 1 round
        let mut words = vec![];
        let mut it = padded_bytes.chunks_exact(32);
        for chunk in &mut it {
            let word = BigUint::from_bytes_be(chunk);
            words.push(word);
        }
        if it.remainder().len() != 0 {
            let mut buffer = [0u8; 32];
            buffer[..it.remainder().len()].copy_from_slice(it.remainder());
            let word = BigUint::from_bytes_be(&buffer);
            words.push(word);
        }

        use sha3::{Digest, Keccak256};

        let mut code_hash = Keccak256::new();
        code_hash.update(&input_bytes);
        let code_hash = code_hash.finalize();
        println!("{}", hex::encode(&code_hash));

        let mut key = UInt256::<E>::zero();
        key.inner[3] = UInt64::from_uint(num_rounds as u64); // num rounds

        use crate::scheduler::queues::{StorageLogQueue, StorageLogRecord};

        let precompile_call_log = StorageLogRecord {
            address: UInt160::<E>::from_uint(u160::from_u64(KECCAK256_PRECOMPILE_ADDRESS)),
            key,
            read_value: UInt256::<E>::zero(),
            written_value: UInt256::<E>::zero(),
            r_w_flag: Boolean::constant(false),
            aux_byte: aux_byte_for_precompile_call::<E>(),
            rollback: Boolean::constant(false),
            is_service: Boolean::constant(false),
            shard_id: Byte::<E>::zero(),
            tx_number_in_block: UInt16::<E>::zero(),
            timestamp: UInt32::<E>::zero(),
        };

        let keccak_gadget = Keccak256Gadget::new(
            cs,
            None,
            None,
            None,
            None,
            true,
            RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME,
        )?;

        let bytes: Vec<_> = input_bytes.iter().map(|el| Byte::constant(*el)).collect();
        let result = keccak_gadget.digest_from_bytes(cs, &bytes)?;

        let mut queue = StorageLogQueue::empty();
        queue.push(
            cs,
            &precompile_call_log,
            &Boolean::constant(true),
            &committer,
        )?;

        let mut memory_queue = MemoryQueriesQueue::empty();
        use cs_empty::CircuitEmpty;
        let mut initial_state = KeccakPrecompileState::<E>::empty();
        initial_state.read_precompile_call = Boolean::constant(true); // IMPORTANT

        let n = cs.n();
        let limit = 1;
        let final_state = keccak256_precompile_inner(
            cs,
            &mut memory_queue,
            &mut queue,
            Some(vec![words]),
            initial_state,
            &committer,
            limit,
        )?;

        let n = cs.n() - n;
        println!("Roughly {} gates per round", n / limit);

        let is_empty = queue.is_empty(cs)?;
        assert!(is_empty.get_value().unwrap());

        assert!(!final_state.read_precompile_call.get_value().unwrap());
        assert!(!final_state
            .read_unaligned_words_for_round
            .get_value()
            .unwrap());
        assert!(final_state.completed.get_value().unwrap());

        assert!(cs.is_satisfied());

        Ok(())
    }

    #[test]
    fn test_hash_one_two_rounds() -> Result<(), SynthesisError> {
        let (mut dummy_cs, committer, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;
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

        let mut rng = deterministic_rng();
        let mut input_length = 200;
        let num_rounds = 2;
        let mut input_bytes = vec![];
        for _ in 0..input_length {
            input_bytes.push(rng.gen::<u8>());
        }

        println!("Input = {}", hex::encode(&input_bytes));

        let padded_bytes = apply_keccak256_padding(&input_bytes);
        println!("Padded input = {}", hex::encode(&padded_bytes));
        // manual padding for 1 round
        let mut words = vec![];
        let mut it = padded_bytes.chunks_exact(32);
        for chunk in &mut it {
            let word = BigUint::from_bytes_be(chunk);
            words.push(word);
        }
        if it.remainder().len() != 0 {
            let mut buffer = [0u8; 32];
            buffer[..it.remainder().len()].copy_from_slice(it.remainder());
            let word = BigUint::from_bytes_be(&buffer);
            words.push(word);
        }

        use sha3::{Digest, Keccak256};

        let mut code_hash = Keccak256::new();
        code_hash.update(&input_bytes);
        let code_hash = code_hash.finalize();
        println!("{}", hex::encode(&code_hash));

        // first round state after absorb
        // [0] = d6b158cb96049c10
        // [1] = 7a59d500207f86e8
        // second round state after absorb
        // [0] = fd24f9109aabc02
        // [1] = c3c9c73450105cf6

        let mut key = UInt256::<E>::zero();
        key.inner[3] = UInt64::from_uint(num_rounds as u64); // num rounds

        use crate::scheduler::queues::{StorageLogQueue, StorageLogRecord};

        let precompile_call_log = StorageLogRecord {
            address: UInt160::<E>::from_uint(u160::from_u64(KECCAK256_PRECOMPILE_ADDRESS)),
            key,
            read_value: UInt256::<E>::zero(),
            written_value: UInt256::<E>::zero(),
            r_w_flag: Boolean::constant(false),
            aux_byte: aux_byte_for_precompile_call::<E>(),
            rollback: Boolean::constant(false),
            is_service: Boolean::constant(false),
            shard_id: Byte::<E>::zero(),
            tx_number_in_block: UInt16::<E>::zero(),
            timestamp: UInt32::<E>::zero(),
        };

        // let keccak_gadget = Keccak256Gadget::new(
        //     cs,
        //     None,
        //     None,
        //     None,
        //     None,
        //     true,
        //     RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME
        // )?;

        // let bytes: Vec<_> = input_bytes.iter().map(|el| Byte::constant(*el)).collect();
        // let result = keccak_gadget.digest_from_bytes(cs, &bytes)?;

        let mut queue = StorageLogQueue::empty();
        queue.push(
            cs,
            &precompile_call_log,
            &Boolean::constant(true),
            &committer,
        )?;

        let mut memory_queue = MemoryQueriesQueue::empty();
        use cs_empty::CircuitEmpty;
        let mut initial_state = KeccakPrecompileState::<E>::empty();
        initial_state.read_precompile_call = Boolean::constant(true); // IMPORTANT

        let n = cs.n();
        let limit = 2;
        let final_state = keccak256_precompile_inner(
            cs,
            &mut memory_queue,
            &mut queue,
            Some(vec![words]),
            initial_state,
            &committer,
            limit,
        )?;

        let n = cs.n() - n;
        println!("Roughly {} gates per round", n / limit);

        let is_empty = queue.is_empty(cs)?;
        assert!(is_empty.get_value().unwrap());

        assert!(!final_state.read_precompile_call.get_value().unwrap());
        assert!(!final_state
            .read_unaligned_words_for_round
            .get_value()
            .unwrap());
        assert!(final_state.completed.get_value().unwrap());

        assert!(cs.is_satisfied());

        Ok(())
    }
}
