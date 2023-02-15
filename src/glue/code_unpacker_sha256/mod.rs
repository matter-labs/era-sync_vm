use super::*;
use cs_derive::*;

use crate::glue::traits::*;
use crate::scheduler::queues::FixedWidthEncodingSpongeLikeQueueWitness;
use crate::scheduler::queues::*;

use super::*;
use crate::glue::traits::*;
use crate::vm::primitives::{UInt16, UInt32};
use cs_derive::*;
use num_traits::Zero;

pub mod input;
pub mod memory_query_updated;

use self::input::*;

use self::memory_query_updated::{MemoryQueriesQueue, MemoryQuery};
// We accumulate memory queries and then use a standard validity argument

#[derive(
    Derivative, CSAllocatable, CSWitnessable, CSEqual, CSSelectable, FixedLengthEncodableExt,
)]
#[EncodingLength = "2"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct SortedDecommitmentRequest<E: Engine> {
    pub timestamp: UInt32<E>,
    pub memory_page: UInt32<E>,
    pub hash: UInt256<E>,
}

impl<E: Engine> SortedDecommitmentRequest<E> {
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 2], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.hash.inner[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.hash.inner[1].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.hash.inner[2].inner, shifts[128]);
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.hash.inner[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.memory_page.inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.timestamp.inner, shifts[96]);
        let el1 = lc.into_num(cs)?;

        Ok([el0, el1])
    }
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 2> for SortedDecommitmentRequest<E> {
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

use crate::scheduler::queues::FixedWidthEncodingSpongeLikeQueue;
pub type ContractCodeDecommittmentQueue<E, const AWIDTH: usize, const SWIDTH: usize> =
    FixedWidthEncodingSpongeLikeQueue<E, SortedDecommitmentRequest<E>, 2, AWIDTH, SWIDTH>;

pub fn unpack_code_into_memory_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<CodeDecommitterCircuitInstanceWitness<E>>,
    round_function: &R,
    limit: usize,
) -> Result<AllocatedNum<E>, SynthesisError> {
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

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let sorted_requests_queue_witness =
        project_ref!(witness, sorted_requests_queue_witness).cloned();
    let code_words = project_ref!(witness, code_words).cloned();

    let mut structured_input = CodeDecommitterCycleInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    )?;

    let requests_queue_from_fsm_input = DecommitQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .decommittment_requests_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .decommittment_requests_queue_state
            .tail,
        structured_input
            .hidden_fsm_input
            .decommittment_requests_queue_state
            .length,
    )?;

    let requests_queue_from_passthrough = DecommitQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .sorted_requests_queue_initial_state
            .head,
        structured_input
            .observable_input
            .sorted_requests_queue_initial_state
            .tail,
        structured_input
            .observable_input
            .sorted_requests_queue_initial_state
            .length,
    )?;

    let mut requests_queue = DecommitQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &requests_queue_from_passthrough,
        &requests_queue_from_fsm_input,
    )?;

    if let Some(wit) = sorted_requests_queue_witness {
        requests_queue.witness = wit;
    }

    let memory_queue_from_fsm_input = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input.hidden_fsm_input.memory_queue_state.head,
        structured_input.hidden_fsm_input.memory_queue_state.tail,
        structured_input.hidden_fsm_input.memory_queue_state.length,
    )?;

    let memory_queue_from_passthrough = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .memory_queue_initial_state
            .head,
        structured_input
            .observable_input
            .memory_queue_initial_state
            .tail,
        structured_input
            .observable_input
            .memory_queue_initial_state
            .length,
    )?;

    let mut memory_queue = MemoryQueriesQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &memory_queue_from_passthrough,
        &memory_queue_from_fsm_input,
    )?;

    let mut starting_fsm_state = CodeDecommittmentFSM::empty();
    starting_fsm_state.state_get_from_queue = Boolean::constant(true);

    let initial_state = CodeDecommittmentFSM::conditionally_select(
        cs,
        &structured_input.start_flag,
        &starting_fsm_state,
        &structured_input.hidden_fsm_input.internal_fsm,
    )?;

    let final_state = unpack_code_into_memory_inner(
        cs,
        &mut memory_queue,
        &mut requests_queue,
        code_words,
        round_function,
        initial_state,
        limit,
    )?;

    let final_memory_state = memory_queue.into_state();
    let final_requets_state = requests_queue.into_state();
    // form the final state
    let done = final_state.finished;
    structured_input.completion_flag = done;
    structured_input.observable_output = CodeDecommitterOutputData::empty();

    structured_input.observable_output.memory_queue_final_state =
        FullSpongeLikeQueueState::conditionally_select(
            cs,
            &structured_input.completion_flag,
            &final_memory_state,
            &structured_input.observable_output.memory_queue_final_state,
        )?;

    structured_input.hidden_fsm_output.internal_fsm = final_state;
    structured_input
        .hidden_fsm_output
        .decommittment_requests_queue_state = final_requets_state;
    structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = structured_input_witness {
            assert_eq!(circuit_result, passed_input);
        }
    }

    use crate::inputs::ClosedFormInputCompactForm;

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    // dbg!(compact_form.create_witness());
    use crate::glue::optimizable_queue::commit_encodable_item;
    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();
    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;

    Ok(public_input)
}

use super::*;
use crate::glue::optimizable_queue::{
    fixed_width_hash_into_state_using_optimizer, variable_length_hash,
};
use crate::glue::traits::get_vec_vec_witness_raw_with_hint_on_more_in_subset;
use crate::glue::traits::CircuitFixedLengthEncodableExt;
use crate::scheduler::queues::memory_access::*;
use crate::scheduler::queues::*;
use crate::vm::optimizer::sponge_set::SpongeOptimizer;
use crate::vm::primitives::UInt64;

// we take a request to decommit hash H into memory page X. Following our internal conventions
// we decommit individual elements starting from the index 1 in the page, and later on set a full length
// into index 0. All elements are 32 bytes

pub fn unpack_code_into_memory_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    memory_queue: &mut MemoryQueriesQueue<E, 2, 3>,
    unpack_requests_queue: &mut DecommitQueue<E, 2, 3>,
    mut input_witness: Option<Vec<Vec<BigUint>>>,
    round_function: &R,
    initial_state: CodeDecommittmentFSM<E>,
    limit: usize,
) -> Result<CodeDecommittmentFSM<E>, SynthesisError> {
    assert!(limit <= u32::MAX as usize);
    assert!(cs
        .get_table(crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME)
        .is_ok());

    const POP_QUEUE_OR_WRITE_ID: u64 = 0;
    const FINALIZE_SHA256: u64 = 1;

    use crate::franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget;
    let mut state = initial_state;

    let mut half = E::Fr::one();
    half.double();
    half = half.inverse().unwrap();

    let words_to_bits = Num::Constant(u64_to_fe(32 * 8));

    let shifts = compute_shifts::<E::Fr>();

    let sha256_gadget = Sha256Gadget::new(cs, None, None, false, false, 0, "")?;

    use zkevm_opcode_defs::VersionedHashDef;
    let versioned_hash_top_16_bits =
        (zkevm_opcode_defs::versioned_hash::ContractCodeSha256::VERSION_BYTE as u16) << 8;

    for _cycle in 0..limit {
        // we need exactly 3 sponges per cycle:
        // - two memory reads when we work on the existing decommittment
        // - and may be queue pop before it
        let may_be_new_request: DecommitQuery<E> =
            unpack_requests_queue.pop_first(cs, &state.state_get_from_queue, round_function)?;

        let hash = may_be_new_request.root_hash.as_u256();

        let chunks = hash.inner[3].decompose_into_uint16_in_place(cs)?;

        let version_hash_matches = UInt16::equals(
            cs,
            &chunks[3],
            &UInt16::from_uint(versioned_hash_top_16_bits),
        )?;

        can_not_be_false_if_flagged(cs, &version_hash_matches, &state.state_get_from_queue)?;

        let length_in_words = chunks[2];
        let length_in_words = UInt16::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &length_in_words,
            &UInt16::from_uint(1),
        )?;

        let length_in_rounds = length_in_words.increment_unchecked(cs)?;
        let length_in_rounds = length_in_rounds.inner.mul(cs, &Num::Constant(half))?;
        // length is always a multiple of 2 since we decided so
        constraint_bit_length(cs, &length_in_rounds, 16)?;
        let length_in_rounds = UInt16::from_num_unchecked(length_in_rounds);
        let length_in_bits_may_be =
            UInt32::from_num_unchecked(length_in_words.inner.mul(cs, &words_to_bits)?);
        use crate::franklin_crypto::plonk::circuit::byte::IntoBytes;
        // turn over the endianess
        let as_bytes = hash.into_be_bytes(cs)?;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&as_bytes[15].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&as_bytes[14].inner, shifts[8]);
        lc.add_assign_number_with_coeff(&as_bytes[13].inner, shifts[16]);
        lc.add_assign_number_with_coeff(&as_bytes[12].inner, shifts[24]);
        lc.add_assign_number_with_coeff(&as_bytes[11].inner, shifts[32]);
        lc.add_assign_number_with_coeff(&as_bytes[10].inner, shifts[40]);
        lc.add_assign_number_with_coeff(&as_bytes[9].inner, shifts[48]);
        lc.add_assign_number_with_coeff(&as_bytes[8].inner, shifts[56]);
        lc.add_assign_number_with_coeff(&as_bytes[7].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&as_bytes[6].inner, shifts[72]);
        lc.add_assign_number_with_coeff(&as_bytes[5].inner, shifts[80]);
        lc.add_assign_number_with_coeff(&as_bytes[4].inner, shifts[88]);
        // we IGNORE the highest bytes
        // lc.add_assign_number_with_coeff(&as_bytes[3].inner, shifts[96]);
        // lc.add_assign_number_with_coeff(&as_bytes[2].inner, shifts[104]);
        // lc.add_assign_number_with_coeff(&as_bytes[1].inner, shifts[112]);
        // lc.add_assign_number_with_coeff(&as_bytes[0].inner, shifts[120]);
        let high = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&as_bytes[15 + 16].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&as_bytes[14 + 16].inner, shifts[8]);
        lc.add_assign_number_with_coeff(&as_bytes[13 + 16].inner, shifts[16]);
        lc.add_assign_number_with_coeff(&as_bytes[12 + 16].inner, shifts[24]);
        lc.add_assign_number_with_coeff(&as_bytes[11 + 16].inner, shifts[32]);
        lc.add_assign_number_with_coeff(&as_bytes[10 + 16].inner, shifts[40]);
        lc.add_assign_number_with_coeff(&as_bytes[9 + 16].inner, shifts[48]);
        lc.add_assign_number_with_coeff(&as_bytes[8 + 16].inner, shifts[56]);
        lc.add_assign_number_with_coeff(&as_bytes[7 + 16].inner, shifts[64]);
        lc.add_assign_number_with_coeff(&as_bytes[6 + 16].inner, shifts[72]);
        lc.add_assign_number_with_coeff(&as_bytes[5 + 16].inner, shifts[80]);
        lc.add_assign_number_with_coeff(&as_bytes[4 + 16].inner, shifts[88]);
        lc.add_assign_number_with_coeff(&as_bytes[3 + 16].inner, shifts[96]);
        lc.add_assign_number_with_coeff(&as_bytes[2 + 16].inner, shifts[104]);
        lc.add_assign_number_with_coeff(&as_bytes[1 + 16].inner, shifts[112]);
        lc.add_assign_number_with_coeff(&as_bytes[0 + 16].inner, shifts[120]);
        let low = lc.into_num(cs)?;

        let parts: [_; 2] = [high, low];

        state.num_rounds_left = UInt16::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &length_in_rounds,
            &state.num_rounds_left,
        )?;
        state.length_in_bits = UInt32::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &length_in_bits_may_be,
            &state.length_in_bits,
        )?;
        state.timestamp = UInt32::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &may_be_new_request.timestamp,
            &state.timestamp,
        )?;
        state.current_page = UInt32::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &may_be_new_request.page,
            &state.current_page,
        )?;
        state.hash_to_compare_against = <[Num<E>; 2]>::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &parts,
            &state.hash_to_compare_against,
        )?;
        state.current_index = UInt32::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &UInt32::zero(),
            &state.current_index,
        )?;
        state.sha256_inner_state = <[Num<E>; 8]>::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &Sha256Gadget::iv_as_nums(),
            &state.sha256_inner_state,
        )?;
        state.length_in_bits = UInt32::conditionally_select(
            cs,
            &state.state_get_from_queue,
            &length_in_bits_may_be,
            &state.length_in_bits,
        )?;

        // we decommit if we either decommit or just got a new request
        let t = smart_or(cs, &[state.state_decommit, state.state_get_from_queue])?;
        state.state_decommit = t;
        state.state_get_from_queue = Boolean::constant(false);

        // even though it's not that useful, we will do it in a checked way for ease of witness
        let may_be_num_rounds_left = state.num_rounds_left.decrement_unchecked(cs)?;
        state.num_rounds_left = UInt16::conditionally_select(
            cs,
            &state.state_decommit,
            &may_be_num_rounds_left,
            &state.num_rounds_left,
        )?;

        let last_round = state.num_rounds_left.is_zero(cs)?;
        let finalize = smart_and(cs, &[last_round, state.state_decommit])?;
        let process_second_word = smart_and(cs, &[last_round.not(), state.state_decommit])?;

        // we either pop from the queue, or absorb-decommit, or finalize hash
        let (input_wit_0, _have_more) = if let Some(get_witness) = state.state_decommit.get_value()
        {
            if get_witness {
                get_vec_vec_witness_raw_with_hint_on_more_in_subset(
                    &mut input_witness,
                    BigUint::from(0u64),
                )
            } else {
                (Some(BigUint::from(0u64)), Some(false))
            }
        } else {
            (None, None)
        };

        let (input_wit_1, _have_more) = if let Some(get_witness) = process_second_word.get_value() {
            if get_witness {
                get_vec_vec_witness_raw_with_hint_on_more_in_subset(
                    &mut input_witness,
                    BigUint::from(0u64),
                )
            } else {
                (Some(BigUint::from(0u64)), Some(false))
            }
        } else {
            (None, None)
        };

        let (mem_item_0, mem_item_0_chunks) =
            UInt256::alloc_from_biguint_and_return_u8_chunks(cs, input_wit_0)?;
        let (mem_item_1, mem_item_1_chunks) =
            UInt256::alloc_from_biguint_and_return_u8_chunks(cs, input_wit_1)?;

        // perform two writes. It's never a "pointer" type
        let mem_query_0 = MemoryQuery {
            timestamp: state.timestamp,
            memory_page: state.current_page,
            memory_index: state.current_index,
            rw_flag: Boolean::constant(true),
            value: mem_item_0,
            value_is_ptr: Boolean::constant(false),
        };

        let raw_mem_query_0 = mem_query_0.into_raw_query(cs)?;

        state.current_index = state
            .current_index
            .conditionally_increment_unchecked(cs, &state.state_decommit)?;

        let mem_query_1 = MemoryQuery {
            timestamp: state.timestamp,
            memory_page: state.current_page,
            memory_index: state.current_index,
            rw_flag: Boolean::constant(true),
            value: mem_item_1,
            value_is_ptr: Boolean::constant(false),
        };
        let raw_mem_query_1 = mem_query_1.into_raw_query(cs)?;

        // even if we do not write in practice then we will never use next value too
        state.current_index = state
            .current_index
            .conditionally_increment_unchecked(cs, &process_second_word)?;

        memory_queue.push(cs, &raw_mem_query_0, &state.state_decommit, round_function)?;

        memory_queue.push(cs, &raw_mem_query_1, &process_second_word, round_function)?;

        let mut sha256_input = vec![];
        // mind endianess! out bytes are LE here, but memory is BE
        for chunk in mem_item_0_chunks
            .chunks(4)
            .rev()
            .chain(mem_item_1_chunks.chunks(4).rev())
        {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&chunk[3], shifts[24]);
            lc.add_assign_number_with_coeff(&chunk[2], shifts[16]);
            lc.add_assign_number_with_coeff(&chunk[1], shifts[8]);
            lc.add_assign_number_with_coeff(&chunk[0], shifts[0]);
            let el = lc.into_num(cs)?;
            sha256_input.push(el);
        }

        // then conditionally form the second half of the block

        let mut sha256_padding = vec![];
        sha256_padding.push(Num::Constant(u64_to_fe(1u64 << 31))); // padding of single byte of 1<<7 and some zeroes after
                                                                   // another 6 empty words
        for _ in 1..7 {
            sha256_padding.push(Num::zero());
        }
        // and final word that will encode the bit length of the input
        // and now put bitlength as BE, that is a little unfortunate, and we need to change endianess
        let bytes = state.length_in_bits.into_be_bytes(cs)?;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&bytes[0].inner, shifts[24]);
        lc.add_assign_number_with_coeff(&bytes[1].inner, shifts[16]);
        lc.add_assign_number_with_coeff(&bytes[2].inner, shifts[8]);
        lc.add_assign_number_with_coeff(&bytes[3].inner, shifts[0]);
        let el = lc.into_num(cs)?;
        sha256_padding.push(el);

        assert_eq!(sha256_input.len(), 16);
        assert_eq!(sha256_padding.len(), 8);

        for (dst, src) in sha256_input[8..].iter_mut().zip(sha256_padding.iter()) {
            *dst = Num::conditionally_select(cs, &finalize, src, dst)?;
        }

        let sha256_input: [_; 16] = sha256_input.try_into().unwrap();

        let new_internal_state =
            sha256_gadget.sha256_round_function(cs, state.sha256_inner_state, &sha256_input)?;
        state.sha256_inner_state = <[Num<E>; 8]>::conditionally_select(
            cs,
            &state.state_decommit,
            &new_internal_state,
            &state.sha256_inner_state,
        )?;

        // make it into uint128, and do not forget to ignore highest two bytes
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&new_internal_state[7], shifts[0]);
        lc.add_assign_number_with_coeff(&new_internal_state[6], shifts[32]);
        lc.add_assign_number_with_coeff(&new_internal_state[5], shifts[64]);
        lc.add_assign_number_with_coeff(&new_internal_state[4], shifts[96]);
        let low = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&new_internal_state[3], shifts[0]);
        lc.add_assign_number_with_coeff(&new_internal_state[2], shifts[32]);
        lc.add_assign_number_with_coeff(&new_internal_state[1], shifts[64]);
        // again, ingore highest bytes
        let high = lc.into_num(cs)?;

        let parts: [_; 2] = [high, low];

        // let mut equals = vec![];
        for (lhs, rhs) in parts.iter().zip(state.hash_to_compare_against.iter()) {
            Num::conditionally_enforce_equal(cs, &finalize, &lhs, &rhs)?;
        }

        // finish
        let is_empty = unpack_requests_queue.is_empty(cs)?;
        let done = smart_and(cs, &[is_empty, finalize])?;
        state.finished = smart_or(cs, &[state.finished, done])?;
        let proceed_next = smart_and(cs, &[is_empty.not(), finalize])?;
        state.state_get_from_queue = proceed_next;
        let continue_decommit = process_second_word;
        state.state_decommit = continue_decommit;
    }

    Ok(state)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::testing::*;

    type E = Bn256;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    #[test]
    fn test_unpack_one() -> Result<(), SynthesisError> {
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
        let mut input_length = 96;
        let mut input_bytes = vec![];
        for _ in 0..input_length {
            input_bytes.push(rng.gen::<u8>());
        }

        let mut words = vec![];
        for chunk in input_bytes.chunks(32) {
            let word = BigUint::from_bytes_be(chunk);
            words.push(word);
        }

        use sha2::{Digest, Sha256};

        let mut code_hash = Sha256::new();
        code_hash.update(&input_bytes);
        let code_hash = code_hash.finalize();
        println!("{}", hex::encode(&code_hash));

        let mut code_hash_in_internal_format = [0u8; 32];
        let length_in_words = (input_length / 32) as u16;
        let length_in_words_le = length_in_words.to_be_bytes();
        code_hash_in_internal_format[0] = length_in_words_le[0];
        code_hash_in_internal_format[1] = length_in_words_le[1];
        code_hash_in_internal_format[2..].copy_from_slice(&code_hash.as_slice()[2..]);
        let code_hash =
            UInt256::constant_from_biguint(BigUint::from_bytes_be(&code_hash_in_internal_format));

        use crate::franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget;

        let sha256_gadget = Sha256Gadget::new(cs, None, None, false, false, 0, "")?;

        let bytes: Vec<_> = input_bytes.iter().map(|el| Byte::constant(*el)).collect();
        let result = sha256_gadget.sha256_from_bytes(cs, &bytes)?;

        let decommittment_request = DecommitQuery::<E> {
            timestamp: UInt32::from_uint(1),
            page: UInt32::from_uint(1024),
            root_hash: DecommitHash::AsU256(code_hash),
            is_first: Boolean::constant(true),
        };

        let mut queue = DecommitQueue::empty();
        queue.push(
            cs,
            &decommittment_request,
            &Boolean::constant(true),
            &committer,
        )?;

        let mut memory_queue = MemoryQueriesQueue::empty();
        use cs_empty::CircuitEmpty;
        let mut initial_state = CodeDecommittmentFSM::<E>::empty();
        initial_state.state_get_from_queue = Boolean::constant(true); // IMPORTANT

        let n = cs.n();
        let limit = 16;
        let final_state = unpack_code_into_memory_inner(
            cs,
            &mut memory_queue,
            &mut queue,
            Some(vec![words]),
            &committer,
            initial_state,
            limit,
        )?;

        let n = cs.n() - n;
        println!("Roughly {} gates per round", n / limit);

        let is_empty = queue.is_empty(cs)?;
        assert!(is_empty.get_value().unwrap());

        assert!(!final_state.state_get_from_queue.get_value().unwrap());
        assert!(!final_state.state_decommit.get_value().unwrap());
        assert!(final_state.finished.get_value().unwrap());

        assert!(cs.is_satisfied());

        Ok(())
    }

    #[test]
    fn test_range_check() -> Result<(), SynthesisError> {
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

        // let a = UInt32::alloc_from_witness(cs, Some(1))?;
        let b = UInt64::alloc_from_witness(cs, Some(1 << 56))?;

        // let _ = a.inner.add(cs, &b.inner)?;

        assert!(cs.is_satisfied());

        Ok(())
    }
}
