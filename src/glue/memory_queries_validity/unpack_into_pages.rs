use super::*;
use crate::glue::optimizable_queue::{fixed_width_hash_into_state_using_optimizer, variable_length_hash};
use crate::glue::traits::CircuitFixedLengthEncodableExt;
use crate::glue::traits::get_vec_vec_witness_raw_with_hint_on_more_in_subset;
use crate::scheduler::queues::memory_access::*;
use crate::scheduler::queues::*;
use crate::vm::optimizer::sponge_set::SpongeOptimizer;
use crate::vm::primitives::UInt64;

pub enum MemoryInput<E: Engine> {
    Code([Num<E>; 2]),

    Bytes32Like(UInt256<E>)
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq)]
pub enum MemoryInputWitness<E: Engine> {
    CodeLike([E::Fr; 2]),
    
    Bytes32Like(BigUint)
}

pub fn unpack_into_pages_inner<
    E: Engine, 
    CS: ConstraintSystem<E>, 
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>
>(
    cs: &mut CS,
    queries_queue: &mut MemoryAccessQueue::<E, 2, 3>,
    mut write_requests_queue: DelegatedMemoryWritesQueue<E, 2, 3>,
    mut input_witness: Option<Vec<Vec<MemoryInputWitness<E>>>>,
    round_function: &R,
    initial_timestamp: UInt32<E>,
    limit: usize
) -> Result<(), SynthesisError> {
    assert!(limit <= u32::MAX as usize);
    let mut sponge_optimizer = SpongeOptimizer::new(round_function.clone(), 1);

    const DECOMMIT_ID: u64 = 0;
    const POP_QUEUE_ID: u64 = 1;
    const FINALIZE_RESCUE_PRIME_ID: u64 = 2;

    const INPUT_DATA_LEN_MEM_LOCATION: u16 = 0;

    write_requests_queue.enforce_to_be_not_empty(cs)?;

    let mut commitment_state = R::empty_state();
    let mut hash_to_compare = Num::zero();
    let mut current_index = UInt16::zero();
    let mut current_page = UInt32::zero();
    let mut state_get_from_queue = Boolean::constant(true);
    let mut state_decommit = Boolean::constant(false);
    let mut state_finalize_sponge = Boolean::constant(false);
    let mut ts = initial_timestamp;

    let mut optimizer = SpongeOptimizer::new(round_function.clone(), 2);

    for _cycle in 0..limit {
        // we either pop from the queue, or absorb-decommit, or finalize hash
        let (input_wit, have_more) = if let Some(get_witness) = state_decommit.get_value() {
            if get_witness {
                get_vec_vec_witness_raw_with_hint_on_more_in_subset(&mut input_witness, MemoryInputWitness::CodeLike([E::Fr::zero(); 2]))
            } else {
                (Some(MemoryInputWitness::CodeLike([E::Fr::zero(); 2])), Some(false))
            }
        } else {
            (None, None)
        };

        let is_code_like = if let Some(input_wit) = input_wit.as_ref() {
            match input_wit {
                MemoryInputWitness::CodeLike(..) => Some(true),
                MemoryInputWitness::Bytes32Like(..) => Some(false)
            }
        } else {
            None
        };
        let is_code_like = Boolean::alloc(cs, is_code_like)?;

        let code_wit = if let Some(input_wit) = input_wit.clone() {
            match input_wit {
                MemoryInputWitness::CodeLike(v) => Some(v),
                MemoryInputWitness::Bytes32Like(..) => Some([E::Fr::zero(); 2]),
            }
        } else {
            None
        };
        let mem_wit = if let Some(input_wit) = input_wit {
            match input_wit {
                MemoryInputWitness::CodeLike(..) => Some(BigUint::from(0u64)),
                MemoryInputWitness::Bytes32Like(v) => Some(v)
            }
        } else {
            None
        };

        let mem_item = UInt256::alloc_from_biguint(cs, mem_wit)?;
        let code_item = Num::alloc_multiple(cs, code_wit)?;

        let [t0, t1] = mem_item.into_u128_pair(cs)?;
        let packed_mem_item = [t0.inner, t1.inner];
        let packed_code_item = code_item;
        let to_decommit = <[Num<E>; 2]>::conditionally_select(cs, &is_code_like, &packed_code_item, &packed_mem_item)?;

        let mem_query = MemoryQuery {
            timestamp_meta: Boolean::constant(false), // always before any actual access
            timestamp: ts,
            memory_markers: [Boolean::constant(false); 2],
            memory_page: current_page,
            memory_index: current_index,
            rw_flag: Boolean::constant(true),
            value: mem_item
        };
        let raw_mem_query = mem_query.into_raw_query(cs)?;

        // we do not care about overflow here as not too long cod is checked in other places,
        // but we check it for simplicity
        let (idx_plus_one, of) = current_index.add(cs, &UInt16::from_uint(1u16))?;
        Boolean::enforce_equal(cs, &of, &Boolean::constant(false))?;
        let (idx_plus_two, of) = idx_plus_one.add(cs, &UInt16::from_uint(1u16))?;
        Boolean::enforce_equal(cs, &of, &Boolean::constant(false))?;

        let code_query_0 = CodeQuery {
            timestamp_meta: Boolean::constant(false), // always before any actual access
            timestamp: ts,
            memory_page: current_page,
            memory_index: current_index,
            rw_flag: Boolean::constant(true),
            value: code_item[0]
        };

        // we are ok to have same TS as keys are different
        let code_query_1 = CodeQuery {
            timestamp_meta: Boolean::constant(false), // always before any actual access
            timestamp: ts,
            memory_page: current_page,
            memory_index: idx_plus_one,
            rw_flag: Boolean::constant(true),
            value: code_item[1]
        };

        let raw_code_query_0 = code_query_0.into_raw_query();
        let raw_code_query_1 = code_query_1.into_raw_query();

        let to_push_mem = raw_mem_query.pack(cs)?;
        let to_push_code_0 = raw_code_query_0.pack(cs)?;
        let to_push_code_1 = raw_code_query_1.pack(cs)?;

        let to_push_raw_0 = <[Num<E>; 2]>::conditionally_select(cs, &is_code_like, &to_push_code_0, &to_push_mem)?;
        let to_push_raw_1 = <[Num<E>; 2]>::conditionally_select(cs, &is_code_like, &to_push_code_1, &[Num::zero(); 2])?;

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
        current_index = UInt16::conditionally_select(cs, &state_get_from_queue, &UInt16::zero(), &current_index)?;

        let new_state = fixed_width_hash_into_state_using_optimizer(
            cs, 
            &to_decommit,
            &commitment_state,
            DECOMMIT_ID,
            state_decommit,
            &mut optimizer
        )?;
        commitment_state = <[Num<E>; 3]>::conditionally_select(cs, &state_decommit, &new_state, &commitment_state)?;
        let increment_by_2 = smart_and(cs, &[state_decommit, is_code_like])?;
        let increment_by_1 = smart_and(cs, &[state_decommit, is_code_like.not()])?;
        current_index = UInt16::conditionally_select(cs, &increment_by_1, &idx_plus_one, &current_index)?;
        current_index = UInt16::conditionally_select(cs, &increment_by_2, &idx_plus_two, &current_index)?;

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

        // push into the queue
        queries_queue.push_raw(cs, &to_push_raw_0, &increment_by_1, round_function)?;
        queries_queue.push_raw(cs, &to_push_raw_1, &increment_by_2, round_function)?;

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

        sponge_optimizer.enforce(cs)?;
    }

    Ok(())
}