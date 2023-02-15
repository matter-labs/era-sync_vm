use super::*;
use crate::glue::optimizable_queue::{fixed_width_hash_into_state_using_optimizer, variable_length_hash};
use crate::glue::traits::CircuitFixedLengthEncodableExt;
use crate::glue::traits::get_vec_vec_witness_raw_with_hint_on_more_in_subset;
use crate::scheduler::queues::memory_access::*;
use crate::scheduler::queues::*;
use crate::vm::optimizer::sponge_set::SpongeOptimizer;
use crate::vm::primitives::UInt64;

// we take a request to decommit hash H into memory page X. Following our internal conventions
// we decommit individual elements starting from the index 1 in the page, and later on set a full length
// into index 0. All elements are 32 bytes

pub fn decommit_into_page_inner<
    E: Engine, 
    CS: ConstraintSystem<E>, 
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>
>(
    cs: &mut CS,
    queries_queue: &mut MemoryAccessQueue::<E, 2, 3>,
    mut write_requests_queue: DelegatedMemoryWritesQueue<E, 2, 3>,
    mut input_witness: Option<Vec<Vec<BigUint>>>,
    round_function: &R,
    initial_timestamp: UInt32<E>,
    limit: usize
) -> Result<UInt32<E>, SynthesisError> {
    assert!(limit <= u32::MAX as usize);

    const DECOMMIT_ID: u64 = 0;
    const POP_QUEUE_ID: u64 = 1;
    const FINALIZE_RESCUE_PRIME_ID: u64 = 2;

    const INPUT_DATA_LEN_MEM_LOCATION: u16 = 0;
    const INPUT_DATA_START_MEM_LOCATION: u16 = 1;

    write_requests_queue.enforce_to_be_not_empty(cs)?;

    let mut commitment_state = R::empty_state();
    let mut hash_to_compare = Num::zero();
    let mut current_index = UInt16::zero();
    let mut current_page = UInt32::zero();
    let mut state_get_from_queue = Boolean::constant(true);
    let mut state_decommit = Boolean::constant(false);
    let mut state_finalize_sponge = Boolean::constant(false);
    let mut ts = initial_timestamp;

    for _cycle in 0..limit {
        // we need exactly 2 sponges per cycle:
        // - one is always busy to perform a memory write, so it's not under the optimizer
        // - another one either pops the queue of requests, or absorbs into state to compute a hash (or finalize it)
        let mut optimizer = SpongeOptimizer::new(round_function.clone(), 1);

        // we either pop from the queue, or absorb-decommit, or finalize hash
        let (input_wit, have_more) = if let Some(get_witness) = state_decommit.get_value() {
            if get_witness {
                get_vec_vec_witness_raw_with_hint_on_more_in_subset(&mut input_witness, BigUint::from(0u64))
            } else {
                (Some(BigUint::from(0u64)), Some(false))
            }
        } else {
            (None, None)
        };

        let mem_item = UInt256::alloc_from_biguint(cs, input_wit)?;
        let [t0, t1] = mem_item.into_u128_pair(cs)?;
        let to_decommit = [t0.inner, t1.inner];

        let mem_location = UInt16::conditionally_select(cs, &state_decommit, &current_index, &UInt16::from_uint(INPUT_DATA_LEN_MEM_LOCATION))?;
        // if we are in a right state then it will indicate a number of decommitted items, otherwise it will never be written
        let mut input_length_as_uint256 = UInt256::zero();
        input_length_as_uint256.inner[0] = UInt64::from_num_unchecked(current_index.inner);
        let value = UInt256::conditionally_select(cs, &state_decommit, &mem_item, &input_length_as_uint256)?;

        let mem_query = MemoryQuery {
            timestamp_meta: Boolean::constant(false), // always before any actual access
            timestamp: ts,
            memory_markers: [Boolean::constant(false); 2],
            memory_page: current_page,
            memory_index: mem_location,
            rw_flag: Boolean::constant(true),
            value: value
        };
        let raw_mem_query = mem_query.into_raw_query(cs)?;

        // we do not care about overflow here as not too long code or input data is checked in other places,
        // but we check it for simplicity
        let (idx_plus_one, of) = current_index.add(cs, &UInt16::from_uint(1u16))?;
        Boolean::enforce_equal(cs, &of, &Boolean::constant(false))?;

        let queue_item = write_requests_queue.pop_first_with_optimizer(
            cs,
            POP_QUEUE_ID,
            &state_get_from_queue,
            &mut optimizer,
        )?;
        let DelegatedMemoryWriteRecord {hash, memory_page} = queue_item;

        hash_to_compare = Num::conditionally_select(cs, &state_get_from_queue, &hash, &hash_to_compare)?;
        current_page = UInt32::conditionally_select(cs, &state_get_from_queue, &memory_page, &current_page)?;
        commitment_state = <[Num<E>; 3]>::conditionally_select(cs, &state_get_from_queue, &R::empty_state(), &commitment_state)?;
        current_index = UInt16::conditionally_select(cs, &state_get_from_queue, &UInt16::from_uint(INPUT_DATA_START_MEM_LOCATION), &current_index)?;

        let new_state = fixed_width_hash_into_state_using_optimizer(
            cs, 
            &to_decommit,
            &commitment_state,
            DECOMMIT_ID,
            state_decommit,
            &mut optimizer
        )?;
        commitment_state = <[Num<E>; 3]>::conditionally_select(cs, &state_decommit, &new_state, &commitment_state)?;
        current_index = UInt16::conditionally_select(cs, &state_decommit, &idx_plus_one, &current_index)?;

        let new_state = fixed_width_hash_into_state_using_optimizer(
            cs, 
            &[Num::Constant(E::Fr::one()), Num::zero()],
            &commitment_state,
            FINALIZE_RESCUE_PRIME_ID,
            state_finalize_sponge,
            &mut optimizer
        )?;

        let try_committment = R::state_into_commitment(new_state)?;
        let hashes_are_equal = Num::equals(cs, &try_committment, &hash_to_compare)?;
        can_not_be_false_if_flagged(cs, &hashes_are_equal, &state_finalize_sponge)?;

        // push into the depending on the state
        // if we decommit - then push into location
        queries_queue.push(cs, &raw_mem_query, &state_decommit, round_function)?;

        // update state
        let can_pop_more_write_requests = write_requests_queue.is_empty(cs)?.not();
        let new_state_get_from_queue = smart_and(cs, &[can_pop_more_write_requests, state_finalize_sponge])?;
        let new_state_decommit = state_get_from_queue;
        let have_more = Boolean::alloc(cs, have_more)?;
        let new_state_finalize_sponge = smart_and(cs, &[state_decommit, have_more])?;

        state_get_from_queue = new_state_get_from_queue;
        state_decommit = new_state_decommit;
        state_finalize_sponge = new_state_finalize_sponge;

        // increment timestamp
        let (new_ts, of) = ts.add(cs, &UInt32::from_uint(1u32))?;
        Boolean::enforce_equal(cs, &of, &Boolean::constant(false))?;
        ts = new_ts;

        optimizer.enforce(cs)?;
    }

    Ok(ts)
}