use super::*;
use crate::glue::traits::*;
use crate::scheduler::queues::*;

// we make a generation aware memory that store all the old and new values
// for a current storage cell. There are largely 3 possible sequences that we must be aware of
// - write_0, .. .... without rollback of the current write
// - write_0, ..., rollback_0, read_0, ... - in this case we must issue and explicit read, even though it's not the first one
// - read_0, ..., - same as above

use crate::glue::optimizable_queue::FixedWidthEncodingGenericQueue;

// We use extra structure with timestamping. Even though we DO have
// timestamp field in StorageLogRecord, such timestamp is the SAME
// for "forward" and "rollback" items, while we do need to have them
// on different timestamps

const TIMESTAMPED_STORAGE_LOG_ENCODING_LEN: usize = 5;

pub mod input;

use cs_derive::*;

#[derive(Derivative, CSAllocatable)]
#[derivative(Clone, Debug)]
pub struct TimestampedStorageLogRecord<E: Engine> {
    pub record: StorageLogRecord<E>,
    pub timestamp: UInt32<E>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq(bound = ""), Eq(bound = ""))]
#[serde(bound = "")]
pub struct TimestampedStorageLogRecordWitness<E: Engine> {
    pub timestamp: u32,
    pub record: StorageLogRecordWitness<E>,
}

pub const EXTENDED_TIMESTAMP_ENCODING_ELEMENT: usize = 1;
pub const EXTENDED_TIMESTAMP_ENCODING_OFFSET: usize = 192;

impl<E: Engine> TimestampedStorageLogRecord<E> {
    pub fn append_timestamp_to_raw_query_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        original_encoding: &[Num<E>; 5],
        timestamp: &UInt32<E>,
    ) -> Result<[Num<E>; 5], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(
            &original_encoding[EXTENDED_TIMESTAMP_ENCODING_ELEMENT],
            shifts[0],
        );
        lc.add_assign_number_with_coeff(
            &timestamp.inner,
            shifts[EXTENDED_TIMESTAMP_ENCODING_OFFSET],
        );
        assert!(EXTENDED_TIMESTAMP_ENCODING_OFFSET + 32 <= E::Fr::CAPACITY as usize);

        let mut result = *original_encoding;
        result[EXTENDED_TIMESTAMP_ENCODING_ELEMENT] = lc.into_num(cs)?;

        Ok(result)
    }
}

impl<E: Engine> TimestampedStorageLogRecord<E> {
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; TIMESTAMPED_STORAGE_LOG_ENCODING_LEN], SynthesisError> {
        let original_encoding = self.record.pack(cs)?;

        Self::append_timestamp_to_raw_query_encoding(cs, &original_encoding, &self.timestamp)
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, TIMESTAMPED_STORAGE_LOG_ENCODING_LEN>
    for TimestampedStorageLogRecord<E>
{
    fn encode<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; TIMESTAMPED_STORAGE_LOG_ENCODING_LEN], SynthesisError> {
        let packed = self.pack(cs)?;

        Ok(packed)
    }
}

impl<E: Engine> CSWitnessable<E> for TimestampedStorageLogRecord<E> {
    type Witness = TimestampedStorageLogRecordWitness<E>;

    fn create_witness(&self) -> Option<Self::Witness> {
        let timestamp = self.timestamp.get_value()?;
        let record = self.record.create_witness()?;

        let wit = TimestampedStorageLogRecordWitness { timestamp, record };

        Some(wit)
    }

    fn placeholder_witness() -> Self::Witness {
        TimestampedStorageLogRecordWitness {
            timestamp: 0u32,
            record: StorageLogRecordWitness::empty(),
        }
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, TIMESTAMPED_STORAGE_LOG_ENCODING_LEN>
    for TimestampedStorageLogRecord<E>
{
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, TIMESTAMPED_STORAGE_LOG_ENCODING_LEN>
    for TimestampedStorageLogRecord<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        <Self as CSAllocatable<E>>::alloc_from_witness(cs, witness)
    }
}

use crate::glue::storage_validity_by_grand_product::input::*;

pub fn sort_and_deduplicate_storage_access_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    closed_form_input: Option<StorageDeduplicatorInstanceWitness<E>>,
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

    inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    let structured_input_witness = project_ref!(closed_form_input, closed_form_input).cloned();
    let unsorted_queue_witness = project_ref!(closed_form_input, unsorted_queue_witness).cloned();
    let intermediate_sorted_queue_witness =
        project_ref!(closed_form_input, intermediate_sorted_queue_witness).cloned();

    let mut structured_input = StorageDeduplicatorInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    )?;

    let unsorted_queue_from_passthrough = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .head_state,
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .tail_state,
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .num_items,
    )?;

    let unsorted_queue_from_fsm_input = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .num_items,
    )?;

    // passthrought must be trivial
    unsorted_queue_from_passthrough
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let mut unsorted_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &unsorted_queue_from_passthrough,
        &unsorted_queue_from_fsm_input,
    )?;

    if let Some(wit) = unsorted_queue_witness {
        unsorted_queue.witness = wit;
    }

    // same logic from sorted
    let intermediate_sorted_queue_from_passthrough = FixedWidthEncodingGenericQueue::<
        E,
        TimestampedStorageLogRecord<E>,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
    >::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .head_state,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .tail_state,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .num_items,
    )?;

    let intermediate_sorted_queue_from_fsm_input = FixedWidthEncodingGenericQueue::<
        E,
        TimestampedStorageLogRecord<E>,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
    >::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .num_items,
    )?;

    // passthrought must be trivial
    intermediate_sorted_queue_from_passthrough
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let mut intermediate_sorted_queue = FixedWidthEncodingGenericQueue::<
        E,
        TimestampedStorageLogRecord<E>,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
    >::conditionally_select(
        cs,
        &structured_input.start_flag,
        &intermediate_sorted_queue_from_passthrough,
        &intermediate_sorted_queue_from_fsm_input,
    )?;

    if let Some(wit) = intermediate_sorted_queue_witness {
        intermediate_sorted_queue.witness = wit;
    }

    // for final sorted queue it's easier

    let empty_final_sorted_queue = StorageLogQueue::<E>::empty();
    let final_sorted_queue_from_fsm_input = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .num_items,
    )?;

    let mut final_sorted_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &empty_final_sorted_queue,
        &final_sorted_queue_from_fsm_input,
    )?;

    // we can always ensure this
    unsorted_queue
        .len()
        .inner
        .enforce_equal(cs, &intermediate_sorted_queue.len().inner)?;

    // get challenges for permutation argument

    let mut fs_input = vec![];
    fs_input.push(unsorted_queue_from_passthrough.get_tail_state());
    fs_input.push(unsorted_queue_from_passthrough.len().inner);
    fs_input.push(intermediate_sorted_queue_from_passthrough.get_tail_state());
    fs_input.push(intermediate_sorted_queue_from_passthrough.len().inner);

    // this is a permutation proof through the grand product
    use crate::glue::optimizable_queue::variable_length_absorb_into_empty_state;
    let mut sponge_state = variable_length_absorb_into_empty_state(cs, &fs_input, round_function)?;

    let mut taken = 0; // up to absorbtion length
    let mut fs_challenges = vec![];
    for _ in 0..NUM_PERMUTATION_ARG_CHALLENGES {
        if taken == 2 {
            // run round
            sponge_state = round_function.round_function(cs, sponge_state)?;
            taken = 0;
        }

        let challenge = sponge_state[taken];
        fs_challenges.push(challenge);

        taken += 1;
    }

    let fs_challenges: [Num<E>; NUM_PERMUTATION_ARG_CHALLENGES] = fs_challenges.try_into().unwrap();

    let initial_lhs = Num::conditionally_select(
        cs,
        &structured_input.start_flag,
        &Num::Constant(E::Fr::one()),
        &structured_input.hidden_fsm_input.lhs_accumulator,
    )?;

    let initial_rhs = Num::conditionally_select(
        cs,
        &structured_input.start_flag,
        &Num::Constant(E::Fr::one()),
        &structured_input.hidden_fsm_input.rhs_accumulator,
    )?;

    // there is no code at address 0 in our case, so we can formally use it for all the purposes
    let previous_packed_key = <[Num<E>; 2]>::conditionally_select(
        cs,
        &structured_input.start_flag,
        &[Num::zero(); 2],
        &structured_input.hidden_fsm_input.previous_packed_key,
    )?;

    let cycle_idx = UInt32::conditionally_select(
        cs,
        &structured_input.start_flag,
        &UInt32::zero(),
        &structured_input.hidden_fsm_input.cycle_idx,
    )?;

    let (
        new_lhs,
        new_rhs,
        cycle_idx,
        previous_packed_key,
        previous_key,
        previous_address,
        previous_timestamp,
        this_cell_has_explicit_read_and_rollback_depth_zero,
        this_cell_base_value,
        this_cell_current_value,
        this_cell_current_depth,
        previous_shard_id,
    ) = sort_and_deduplicate_storage_access_inner(
        cs,
        initial_lhs,
        initial_rhs,
        &mut unsorted_queue,
        &mut intermediate_sorted_queue,
        &mut final_sorted_queue,
        structured_input.start_flag,
        cycle_idx,
        fs_challenges,
        previous_packed_key,
        structured_input.hidden_fsm_input.previous_key,
        structured_input.hidden_fsm_input.previous_address,
        structured_input.hidden_fsm_input.previous_timestamp,
        structured_input
            .hidden_fsm_input
            .this_cell_has_explicit_read_and_rollback_depth_zero,
        structured_input.hidden_fsm_input.this_cell_base_value,
        structured_input.hidden_fsm_input.this_cell_current_value,
        structured_input.hidden_fsm_input.this_cell_current_depth,
        structured_input.hidden_fsm_input.previous_shard_id,
        round_function,
        limit,
    )?;

    let unsorted_is_empty = unsorted_queue.is_empty(cs)?;
    let sorted_is_empty = intermediate_sorted_queue.is_empty(cs)?;

    Boolean::enforce_equal(cs, &unsorted_is_empty, &sorted_is_empty)?;

    let completed = smart_and(cs, &[unsorted_is_empty, sorted_is_empty])?;
    Num::conditionally_enforce_equal(cs, &completed, &new_lhs, &new_rhs)?;

    // form the input/output

    structured_input.hidden_fsm_output.cycle_idx = cycle_idx;
    structured_input.hidden_fsm_output.previous_packed_key = previous_packed_key;
    structured_input.hidden_fsm_output.previous_key = previous_key;
    structured_input.hidden_fsm_output.previous_address = previous_address;
    structured_input.hidden_fsm_output.previous_timestamp = previous_timestamp;
    structured_input
        .hidden_fsm_output
        .this_cell_has_explicit_read_and_rollback_depth_zero =
        this_cell_has_explicit_read_and_rollback_depth_zero;
    structured_input.hidden_fsm_output.this_cell_base_value = this_cell_base_value;
    structured_input.hidden_fsm_output.this_cell_current_value = this_cell_current_value;
    structured_input.hidden_fsm_output.this_cell_current_depth = this_cell_current_depth;
    structured_input.hidden_fsm_output.previous_shard_id = previous_shard_id;

    structured_input.hidden_fsm_output.lhs_accumulator = new_lhs;
    structured_input.hidden_fsm_output.rhs_accumulator = new_rhs;

    structured_input
        .hidden_fsm_output
        .current_unsorted_queue_state = unsorted_queue.into_state();
    structured_input
        .hidden_fsm_output
        .current_intermediate_sorted_queue_state = intermediate_sorted_queue.into_state();

    structured_input.completion_flag = completed;

    let final_queue_for_observable_output = FixedWidthEncodingGenericQueue::conditionally_select(
        cs,
        &completed,
        &final_sorted_queue,
        &FixedWidthEncodingGenericQueue::empty(),
    )?;

    structured_input.observable_output.final_sorted_queue_state =
        final_queue_for_observable_output.into_state();

    structured_input
        .hidden_fsm_output
        .current_final_sorted_queue_state = final_sorted_queue.into_state();

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

const NUM_PERMUTATION_ARG_CHALLENGES: usize = TIMESTAMPED_STORAGE_LOG_ENCODING_LEN + 1;

pub fn sort_and_deduplicate_storage_access_inner<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    mut lhs: Num<E>,
    mut rhs: Num<E>,
    original_queue: &mut StorageLogQueue<E>,
    intermediate_sorted_queue: &mut FixedWidthEncodingGenericQueue<
        E,
        TimestampedStorageLogRecord<E>,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
    >,
    sorted_queue: &mut StorageLogQueue<E>,
    is_start: Boolean,
    mut cycle_idx: UInt32<E>,
    fs_challenges: [Num<E>; NUM_PERMUTATION_ARG_CHALLENGES],
    mut previous_packed_key: [Num<E>; 2],
    mut previous_key: UInt256<E>,
    mut previous_address: UInt160<E>,
    mut previous_timestamp: UInt32<E>,
    mut this_cell_has_explicit_read_and_rollback_depth_zero: Boolean,
    mut this_cell_base_value: UInt256<E>,
    mut this_cell_current_value: UInt256<E>,
    mut this_cell_current_depth: UInt32<E>,
    mut previous_shard_id: Byte<E>,
    round_function: &R,
    limit: usize,
) -> Result<
    (
        Num<E>,
        Num<E>,
        UInt32<E>,
        [Num<E>; 2],
        UInt256<E>,
        UInt160<E>,
        UInt32<E>,
        Boolean,
        UInt256<E>,
        UInt256<E>,
        UInt32<E>,
        Byte<E>,
    ),
    SynthesisError,
> {
    assert!(limit <= u32::MAX as usize);

    // we can recreate it here, there are two cases:
    // - we are 100% empty, but it's the only circuit in this case
    // - otherwise we continue, and then it's not trivial
    let no_work = original_queue.is_empty(cs)?;
    let mut previous_item_is_trivial = smart_or(cs, &[no_work, is_start])?;

    let additive_part = *fs_challenges.last().unwrap();

    // we simultaneously pop, accumulate partial product,
    // and decide whether or not we should move to the next cell

    // to ensure uniqueness we place timestamps in a addition to the

    const PACKED_WIDTHS: [usize; 2] = [192, 232];

    for _cycle in 0..limit {
        let original_timestamp = cycle_idx;
        // increment it immediatelly
        let new_cycle_idx = cycle_idx.increment_unchecked(cs)?;
        cycle_idx = new_cycle_idx;

        let original_is_empty = original_queue.is_empty(cs)?;
        let sorted_is_empty = intermediate_sorted_queue.is_empty(cs)?;
        Boolean::enforce_equal(cs, &original_is_empty, &sorted_is_empty)?;

        let should_pop = original_is_empty.not();
        let item_is_trivial = original_is_empty;

        let original_encoding = original_queue.pop_first_encoding_only::<_, _, 2, 3>(
            cs,
            &should_pop,
            round_function,
        )?;
        let (sorted_item, sorted_encoding) = intermediate_sorted_queue
            .pop_first_and_return_encoding(cs, &should_pop, round_function)?;
        let extended_original_encoding =
            TimestampedStorageLogRecord::append_timestamp_to_raw_query_encoding(
                cs,
                &original_encoding,
                &original_timestamp,
            )?;

        assert_eq!(extended_original_encoding.len(), sorted_encoding.len());
        assert_eq!(extended_original_encoding.len(), fs_challenges.len() - 1);

        // accumulate into product

        let mut lhs_lc = LinearCombination::zero();
        let mut rhs_lc = LinearCombination::zero();
        for ((original_el, sorted_el), challenge) in extended_original_encoding
            .into_iter()
            .zip(sorted_encoding.into_iter())
            .zip(fs_challenges.iter())
        {
            let lhs_contribution = original_el.mul(cs, &challenge)?;
            let rhs_contribution = sorted_el.mul(cs, &challenge)?;

            lhs_lc.add_assign_number_with_coeff(&lhs_contribution, E::Fr::one());
            rhs_lc.add_assign_number_with_coeff(&rhs_contribution, E::Fr::one());
        }

        lhs_lc.add_assign_number_with_coeff(&additive_part, E::Fr::one());
        rhs_lc.add_assign_number_with_coeff(&additive_part, E::Fr::one());

        let lhs_contribution = lhs_lc.into_num(cs)?;
        let rhs_contribution = rhs_lc.into_num(cs)?;

        let lhs_candidate = lhs.mul(cs, &lhs_contribution)?;
        let rhs_candidate = rhs.mul(cs, &rhs_contribution)?;

        lhs = Num::conditionally_select(cs, &should_pop, &lhs_candidate, &lhs)?;
        rhs = Num::conditionally_select(cs, &should_pop, &rhs_candidate, &rhs)?;

        let TimestampedStorageLogRecord { record, timestamp } = sorted_item;

        // now resolve a logic about sorting itself
        let packed_key = pack_key(
            cs,
            (record.shard_id.clone(), record.address.clone(), record.key),
        )?;

        // ensure sorting
        let (keys_are_equal, previous_key_is_greater) =
            prepacked_long_comparison(cs, &previous_packed_key, &packed_key, &PACKED_WIDTHS)?;

        can_not_be_false_if_flagged(cs, &previous_key_is_greater.not(), &item_is_trivial.not())?;

        // if keys are the same then timestamps are sorted
        let (_, previous_timestamp_is_less) = previous_timestamp.sub(cs, &timestamp)?;
        // enforce if keys are the same and not trivial
        let must_enforce = smart_and(cs, &[keys_are_equal, item_is_trivial.not()])?;
        can_not_be_false_if_flagged(cs, &previous_timestamp_is_less, &must_enforce)?;

        // we follow the procedure:
        // if keys are different then we finish with a previous one and update parameters
        // else we just update parameters

        // if new cell
        {
            if _cycle == 0 {
                // it must always be true if we start
                can_not_be_false_if_flagged(cs, &keys_are_equal.not(), &is_start)?;
            }
            // finish with the old one
            // if somewhere along the way we did encounter a read at rollback depth zero (not important if there were such),
            // and if current rollback depth is 0 then we MUST issue a read

            let value_is_unchanged =
                UInt256::equals(cs, &this_cell_current_value, &this_cell_base_value)?;
            // there may be a situation when as a result of sequence of writes
            // storage slot is CLAIMED to be unchanged. There are two options:
            // - unchanged because we had write - ... - rollback AND we do not have read at depth 0.
            //   In this case we used a temporary value, and the fact that the last action is rollback
            //   all the way to the start (to depth 0), we are not interested in what was an initial value
            // - unchanged because a -> write b -> ... -> write a AND we do or do not have read at depth 0.
            //   In this case we would not need to write IF prover is honest and provides a true witness to "read value"
            //   field at the first write. But we can not rely on this and have to check this fact!
            let current_depth_is_zero = this_cell_current_depth.is_zero(cs)?;
            let unchanged_but_not_by_rollback =
                smart_and(cs, &[value_is_unchanged, current_depth_is_zero.not()])?;
            let issue_protective_read = smart_or(
                cs,
                &[
                    this_cell_has_explicit_read_and_rollback_depth_zero,
                    unchanged_but_not_by_rollback,
                ],
            )?;
            let should_write = value_is_unchanged.not();

            let query = StorageLogRecord {
                address: previous_address,
                key: previous_key,
                read_value: this_cell_base_value,
                written_value: this_cell_current_value,
                r_w_flag: should_write,
                aux_byte: Byte::zero(),
                rollback: Boolean::constant(false),
                is_service: Boolean::constant(false),
                shard_id: previous_shard_id,
                tx_number_in_block: UInt16::zero(),
                timestamp: UInt32::zero(),
            };

            // if we did only writes and rollbacks then we don't need to update
            let should_update = smart_or(cs, &[issue_protective_read, should_write])?;
            let should_push = smart_and(
                cs,
                &[
                    previous_item_is_trivial.not(),
                    keys_are_equal.not(),
                    should_update,
                ],
            )?;

            sorted_queue.push(cs, &query, &should_push, round_function)?;

            let new_non_trivial_cell =
                smart_and(cs, &[item_is_trivial.not(), keys_are_equal.not()])?;

            // and update as we switch to the new cell with extra logic
            let meaningful_value = UInt256::conditionally_select(
                cs,
                &record.r_w_flag,
                &record.written_value,
                &record.read_value,
            )?;

            // re-update
            this_cell_base_value = UInt256::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &record.read_value,
                &this_cell_base_value,
            )?;

            this_cell_current_value = UInt256::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &meaningful_value,
                &this_cell_current_value,
            )?;

            let rollback_depth_for_new_cell = UInt32::conditionally_select(
                cs,
                &record.r_w_flag,
                &UInt32::from_uint(1),
                &UInt32::zero(),
            )?;

            this_cell_current_depth = UInt32::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &rollback_depth_for_new_cell,
                &this_cell_current_depth,
            )?;

            // we have new non-trivial
            // and if it's read then it's definatelly at depth 0
            this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &record.r_w_flag.not(),
                &this_cell_has_explicit_read_and_rollback_depth_zero,
            )?;
        }

        // if same cell - update
        {
            let non_trivial_and_same_cell =
                smart_and(cs, &[item_is_trivial.not(), keys_are_equal])?;
            let non_trivial_read_of_same_cell =
                smart_and(cs, &[non_trivial_and_same_cell, record.r_w_flag.not()])?;
            let non_trivial_write_of_same_cell =
                smart_and(cs, &[non_trivial_and_same_cell, record.r_w_flag])?;
            let write_no_rollback =
                smart_and(cs, &[non_trivial_write_of_same_cell, record.rollback.not()])?;
            let write_rollback = smart_and(cs, &[non_trivial_write_of_same_cell, record.rollback])?;

            // update rollback depth the is a result of this action
            this_cell_current_depth = this_cell_current_depth
                .conditionally_increment_unchecked(cs, &write_no_rollback)?;
            this_cell_current_depth =
                this_cell_current_depth.conditionally_decrement_unchecked(cs, &write_rollback)?;

            // check consistency
            let read_is_equal_to_current =
                UInt256::equals(cs, &this_cell_current_value, &record.read_value)?;

            can_not_be_false_if_flagged(
                cs,
                &read_is_equal_to_current,
                &non_trivial_read_of_same_cell,
            )?;

            // decide to update
            this_cell_current_value = UInt256::conditionally_select(
                cs,
                &write_no_rollback,
                &record.written_value,
                &this_cell_current_value,
            )?;

            this_cell_current_value = UInt256::conditionally_select(
                cs,
                &write_rollback,
                &record.read_value,
                &this_cell_current_value,
            )?;

            let current_rollback_depth_is_zero = this_cell_current_depth.is_zero(cs)?;
            let read_at_rollback_depth_zero_of_same_cell = smart_and(
                cs,
                &[
                    current_rollback_depth_is_zero,
                    non_trivial_read_of_same_cell,
                ],
            )?;

            this_cell_base_value = UInt256::conditionally_select(
                cs,
                &read_at_rollback_depth_zero_of_same_cell,
                &record.read_value,
                &this_cell_base_value,
            )?;

            // we definately read non-trivial, and that is on depth 0, so set to true
            this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
                cs,
                &read_at_rollback_depth_zero_of_same_cell,
                &Boolean::constant(true),
                &this_cell_has_explicit_read_and_rollback_depth_zero,
            )?;
        }

        // always update counters
        previous_shard_id = record.shard_id;
        previous_address = record.address;
        previous_key = record.key;
        previous_item_is_trivial = item_is_trivial;
        previous_timestamp = timestamp;
        previous_packed_key = packed_key;
    }

    // finalization step - out of cycle, and only if we are done just yet
    {
        let queues_exhausted = original_queue.is_empty(cs)?;

        // cell state is final
        let value_is_unchanged =
            UInt256::equals(cs, &this_cell_current_value, &this_cell_base_value)?;
        let current_depth_is_zero = this_cell_current_depth.is_zero(cs)?;
        let unchanged_but_not_by_rollback =
            smart_and(cs, &[value_is_unchanged, current_depth_is_zero.not()])?;
        let issue_protective_read = smart_or(
            cs,
            &[
                this_cell_has_explicit_read_and_rollback_depth_zero,
                unchanged_but_not_by_rollback,
            ],
        )?;
        let should_write = value_is_unchanged.not();

        let query = StorageLogRecord {
            address: previous_address,
            key: previous_key,
            read_value: this_cell_base_value,
            written_value: this_cell_current_value,
            r_w_flag: should_write,
            aux_byte: Byte::zero(),
            rollback: Boolean::constant(false),
            is_service: Boolean::constant(false),
            shard_id: previous_shard_id,
            tx_number_in_block: UInt16::zero(),
            timestamp: UInt32::zero(),
        };

        // if we did only writes and rollbacks then we don't need to update
        let should_update = smart_or(cs, &[issue_protective_read, should_write])?;
        let should_push = smart_and(
            cs,
            &[
                previous_item_is_trivial.not(),
                should_update,
                queues_exhausted,
            ],
        )?;

        sorted_queue.push(cs, &query, &should_push, round_function)?;

        // reset flag to match simple witness generation convensions
        this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
            cs,
            &queues_exhausted,
            &Boolean::constant(false),
            &this_cell_has_explicit_read_and_rollback_depth_zero,
        )?;
    }

    // output our FSM values

    Ok((
        lhs,
        rhs,
        cycle_idx,
        previous_packed_key,
        previous_key,
        previous_address,
        previous_timestamp,
        this_cell_has_explicit_read_and_rollback_depth_zero,
        this_cell_base_value,
        this_cell_current_value,
        this_cell_current_depth,
        previous_shard_id,
    ))
}

pub fn pack_key<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    key_tuple: (Byte<E>, UInt160<E>, UInt256<E>),
) -> Result<[Num<E>; 2], SynthesisError> {
    assert!(E::Fr::CAPACITY >= 232);
    let shifts = compute_shifts::<E::Fr>();

    // LE packing

    let (shard_id, address, key) = key_tuple;
    let mut lc_0 = LinearCombination::zero();
    lc_0.add_assign_number_with_coeff(&key.inner[0].inner, shifts[0]);
    lc_0.add_assign_number_with_coeff(&key.inner[1].inner, shifts[64]);
    lc_0.add_assign_number_with_coeff(&key.inner[2].inner, shifts[128]);
    // 192 in total
    let value_0 = lc_0.into_num(cs)?;

    let mut lc_1 = LinearCombination::zero();
    lc_1.add_assign_number_with_coeff(&key.inner[3].inner, shifts[0]);
    lc_1.add_assign_number_with_coeff(&address.inner, shifts[64]);
    lc_1.add_assign_number_with_coeff(&shard_id.inner, shifts[160 + 64]);
    let value_1 = lc_1.into_num(cs)?;
    // 64 + 160 + 8 = 232 in total

    Ok([value_0, value_1])
}
