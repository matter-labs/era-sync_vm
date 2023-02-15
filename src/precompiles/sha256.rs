use super::*;

use crate::circuit_structures::traits::*;
use crate::franklin_crypto::plonk::circuit::byte::*;
use crate::franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::*;
use crate::glue::aux_byte_markers::*;
use crate::glue::optimizable_queue::*;
use crate::glue::sha256_round_function_circuit::input::Sha256RoundFunctionFSM;
use crate::glue::sha256_round_function_circuit::Sha256PrecompileCallParams;
use crate::glue::traits::get_vec_vec_witness_raw_with_hint_on_more_in_subset;
use crate::traits::*;
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

pub const MEMORY_READ_QUERIES_PER_CYCLE: usize = 2;
pub const SHA256_PRECOMPILE_ADDRESS: u64 = 0x02;
use crate::scheduler::queues::StorageLogQueue;

pub fn sha256_precompile_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    memory_queue: &mut MemoryQueriesQueue<E, 2, 3>,
    precompile_calls_queue: &mut StorageLogQueue<E>,
    mut input_witness: Option<Vec<Vec<BigUint>>>,
    state: Sha256RoundFunctionFSM<E>,
    round_function: &R,
    limit: usize,
) -> Result<Sha256RoundFunctionFSM<E>, SynthesisError> {
    assert!(limit <= u32::MAX as usize);
    assert!(cs
        .get_table(crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME)
        .is_ok());

    let mut state = state;
    assert!(limit <= u32::MAX as usize);

    let precompile_address = UInt160::<E>::from_uint(u160::from_u64(SHA256_PRECOMPILE_ADDRESS));
    let aux_byte_for_precompile = aux_byte_for_precompile_call::<E>();

    // let sha256_gadget = Sha256Gadget::new(
    //     cs,
    //     None,
    //     None,
    //     false,
    //     true,
    //     16,
    //     RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME
    // )?;

    let sha256_gadget = Sha256Gadget::new(cs, None, None, false, false, 0, "")?;

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
        let call_params = Sha256PrecompileCallParams::from_encoding(cs, params_encoding)?;

        state.precompile_call_params = Sha256PrecompileCallParams::conditionally_select(
            cs,
            &state.read_precompile_call,
            &call_params,
            &state.precompile_call_params,
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

        let reset_buffer = smart_or(cs, &[state.read_precompile_call, state.completed])?;
        state.read_words_for_round = smart_or(
            cs,
            &[state.read_precompile_call, state.read_words_for_round],
        )?;
        state.read_precompile_call = Boolean::constant(false);

        // ---------------------------------
        // Now perform few memory queries to read content

        let zero_rounds_left = state.precompile_call_params.num_rounds.is_zero(cs)?;

        let mut memory_queries_as_u32_words = vec![];
        let should_read = zero_rounds_left.not();
        for _i in 0..MEMORY_READ_QUERIES_PER_CYCLE {
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
            memory_query.memory_page = state.precompile_call_params.input_page;
            memory_query.memory_index = state.precompile_call_params.input_offset;
            memory_query.rw_flag = Boolean::constant(false);
            memory_query.value = u256_value;

            state.precompile_call_params.input_offset =
                state
                    .precompile_call_params
                    .input_offset
                    .conditionally_increment_unchecked(cs, &state.read_words_for_round)?;
            let raw_query = memory_query.into_raw_query(cs)?;
            // perform read
            memory_queue.push(cs, &raw_query, &should_read, round_function)?;

            // proper order of words, and of bytes
            let mut be_bytes = le_bytes;
            be_bytes.reverse();
            for chunk in be_bytes.chunks(4) {
                let mut chunk: [Byte<E>; 4] = chunk
                    .iter()
                    .map(|el| Byte::from_num_unconstrained(cs, *el))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                // SHA256 interprets 4 bytes as BE integer, so we reverse twice
                chunk.reverse();
                let be_integer = UInt32::from_bytes_le(cs, &chunk)?;
                memory_queries_as_u32_words.push(be_integer);
            }
        }

        state.precompile_call_params.num_rounds = state
            .precompile_call_params
            .num_rounds
            .conditionally_decrement_unchecked(cs, &state.read_words_for_round)?;

        // absorb

        let input: [Num<E>; 16] = memory_queries_as_u32_words
            .into_iter()
            .map(|el| el.inner)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let sha256_empty_internal_state = Sha256Gadget::iv_as_nums();

        let current_sha256_state = <[Num<E>; 8]>::conditionally_select(
            cs,
            &reset_buffer,
            &sha256_empty_internal_state,
            &state.sha256_inner_state,
        )?;

        let new_state = sha256_gadget.sha256_round_function(cs, current_sha256_state, &input)?;

        state.sha256_inner_state = new_state;

        let no_rounds_left = state.precompile_call_params.num_rounds.is_zero(cs)?;
        let write_result = smart_and(cs, &[state.read_words_for_round, no_rounds_left])?;

        // we reinterpret byte order
        let shifts = compute_shifts::<E::Fr>();
        let mut result = UInt256::zero();
        for (idx, pair) in new_state.chunks(2).enumerate() {
            let high = pair[0];
            let low = pair[1];

            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&low, shifts[0]);
            lc.add_assign_number_with_coeff(&high, shifts[32]);
            result.inner[3 - idx] = UInt64::from_num_unchecked(lc.into_num(cs)?);
        }

        // if write_result.get_value().unwrap_or(false) {
        //     println!("Result = {}", result.get_value().unwrap().to_str_radix(16));
        // }

        let mut write_query = MemoryQuery::empty();
        write_query.timestamp = state.timestamp_to_use_for_write;
        write_query.memory_page = state.precompile_call_params.output_page;
        write_query.memory_index = state.precompile_call_params.output_offset;
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
        state.read_words_for_round =
            smart_or(cs, &[state.read_precompile_call, state.completed])?.not();
    }

    Ok(state)
}
