use super::*;

const SORTING_KEY_ENCODING_LENGTHS: [usize; 1] = [32 + 1 + 16 + 32];

fn sorting_key_key_value_and_rw_flags<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, query: &RawMemoryQuery<E>) -> Result<(Num<E>, Num<E>, [Num<E>; 2], Boolean), SynthesisError> {
    // key is memory_page | index | ts_marker | ts
    let RawMemoryQuery {
        timestamp,
        timestamp_meta,
        memory_index,
        memory_page,
        rw_flag,
        value_residual,
        value,
        ..
    } = query;

    let shifts = compute_shifts::<E::Fr>();
    let mut lc = LinearCombination::zero();
    let mut shift = 0;
    lc.add_assign_number_with_coeff(&memory_index.inner, shifts[shift]);
    shift += 16;
    lc.add_assign_number_with_coeff(&memory_page.inner, shifts[shift]);
    shift += 32;
    assert!(shift <= E::Fr::CAPACITY as usize);
    let meaningfull_key = lc.into_num(cs)?;
    let k_width = shift;

    let mut lc = LinearCombination::zero();
    let mut shift = 0;
    lc.add_assign_number_with_coeff(&timestamp.inner, shifts[shift]);
    shift += 32;
    lc.add_assign_boolean_with_coeff(&timestamp_meta, shifts[shift]);
    shift += 1;
    lc.add_assign_number_with_coeff(&meaningfull_key, shifts[shift]);
    shift += k_width;
    assert!(shift <= E::Fr::CAPACITY as usize);
    assert_eq!(shift, SORTING_KEY_ENCODING_LENGTHS[0]);
    let sorting_key = lc.into_num(cs)?;

    let v0 = value_residual.inner;
    let v1 = *value;

    let t = (sorting_key, meaningfull_key, [v0, v1], *rw_flag);

    Ok(t)
}

pub fn partial_accumulate_inner<
    E: Engine, 
    CS: ConstraintSystem<E>, 
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>
>(
    cs: &mut CS,
    unsorted_queue: &mut MemoryAccessQueue::<E, 2, 3>,
    sorted_queuee: &mut MemoryAccessQueue::<E, 2, 3>,
    fs_challenges: &[Num<E>; 3],
    initial_lhs: Num<E>,
    initial_rhs: Num<E>,
    continue_argument: Boolean,
    previous_sk: Num<E>,
    previous_full_key: Num<E>,
    last_element_values: [Num<E>; 2],
    round_function: &R,
    limit: usize
) -> Result<((Num<E>, Num<E>), (Num<E>, Num<E>, [Num<E>; 2])), SynthesisError> {
    assert!(limit <= u32::MAX as usize);
    let mut lhs = initial_lhs;
    let mut rhs = initial_rhs;

    let [challenge_0, challenge_1, additive_part] = *fs_challenges;

    let [v0, v1] = last_element_values;
    let mut previous_key_value = (previous_sk, previous_full_key, (v0, v1));

    for _cycle in 0..limit {
        let can_pop_from_unsorted_queue = unsorted_queue.is_empty(cs)?.not();
        let can_pop_from_sorted_queue = sorted_queuee.is_empty(cs)?.not();
        Boolean::enforce_equal(cs, &can_pop_from_unsorted_queue, &can_pop_from_sorted_queue)?;
        let can_pop = can_pop_from_unsorted_queue;
        // let (_unsorted_item, unsorted_item_encoding) = unsorted_queue.pop_first_and_return_encoding(cs, &can_pop, round_function)?;
        let unsorted_item_encoding = unsorted_queue.pop_first_encoding_only(cs, &can_pop, round_function)?;
        let (sorted_item, sorted_item_encoding) = unsorted_queue.pop_first_and_return_encoding(cs, &can_pop, round_function)?;
        {
            // either continue the argument or do nothin
            let (previous_sk, previous_k, (previous_v0, previous_v1)) = previous_key_value;
            let (sk, k, [v0, v1], rw_flag) = sorting_key_key_value_and_rw_flags(cs, &sorted_item)?;

            // ensure sorting
            let (keys_are_equal, previous_key_is_greater) = prepacked_long_comparison(
                cs, 
                &[previous_sk],
                &[sk],
                &SORTING_KEY_ENCODING_LENGTHS
            )?;
            let keys_are_in_ascending_order = smart_and(cs, &[previous_key_is_greater.not(), keys_are_equal.not()])?;
            if _cycle != 0 {
                can_not_be_false_if_flagged(cs, &keys_are_in_ascending_order, &can_pop)?;
            } else {
                let should_enforce = smart_and(cs, &[can_pop, continue_argument])?;
                can_not_be_false_if_flagged(cs, &keys_are_in_ascending_order, &should_enforce)?;
            }
            
            let same_memory_cell = Num::equals(cs, &previous_k, &k)?;
            let v0_equal = Num::equals(cs, &previous_v0, &v0)?;
            let v1_equal = Num::equals(cs, &previous_v1, &v1)?;

            // check uninit read
            let t0 = v0.is_zero(cs)?;
            let t1 = v1.is_zero(cs)?;
            let is_zero = smart_and(cs, &[t0, t1])?;

            // we only have a difference in these flags at the first step
            if _cycle != 0 {
                let read_uninitialized = smart_and(cs, &[same_memory_cell.not(), rw_flag.not()])?;
                can_not_be_false_if_flagged(cs, &is_zero, &read_uninitialized)?;

                // check standard RW validity
                let value_equal = smart_and(cs, &[v0_equal, v1_equal])?;
                let check_equality = smart_and(cs, &[same_memory_cell, rw_flag.not()])?;
                can_not_be_false_if_flagged(cs, &value_equal, &check_equality)?;
            } else {
                // see if we continue the argument then all our checks should be valid,
                // otherwise only read uninit should be enforced

                // if we start a fresh argument then our comparison
                let read_uninitialized_continue = smart_and(cs, &[continue_argument, same_memory_cell.not(), rw_flag.not()])?;
                let read_uninit_at_start = smart_and(cs, &[continue_argument.not(), rw_flag.not()])?;
                let should_enforce = smart_or(cs, &[read_uninitialized_continue, read_uninit_at_start])?;
                can_not_be_false_if_flagged(cs, &is_zero, &should_enforce)?;

                // check standard RW validity
                let value_equal = smart_and(cs, &[v0_equal, v1_equal])?;
                let check_equality = smart_and(cs, &[same_memory_cell, rw_flag.not(), continue_argument])?;
                can_not_be_false_if_flagged(cs, &value_equal, &check_equality)?;
            }

            previous_key_value = (sk, k, (v0, v1));
        }
        
        // if we did pop then accumulate
        let mut lhs_contribution = LinearCombination::zero();
        lhs_contribution.add_assign_number_with_coeff(&additive_part, E::Fr::one());
        let mut rhs_contribution = LinearCombination::zero();
        rhs_contribution.add_assign_number_with_coeff(&additive_part, E::Fr::one());

        assert_eq!(unsorted_item_encoding.len(), 2);
        assert_eq!(sorted_item_encoding.len(), 2);

        for ((unsorted_contribution, sorted_contribution), challenge) in unsorted_item_encoding.iter().zip(sorted_item_encoding.iter()).zip([challenge_0, challenge_1].iter()) {
            let l = unsorted_contribution.mul(cs, challenge)?;
            lhs_contribution.add_assign_number_with_coeff(&l, E::Fr::one());
            let r = sorted_contribution.mul(cs, challenge)?;
            lhs_contribution.add_assign_number_with_coeff(&r, E::Fr::one());
        }

        let lhs_contribution = lhs_contribution.into_num(cs)?;
        let rhs_contribution = rhs_contribution.into_num(cs)?;
        let new_lhs = lhs.mul(cs, &lhs_contribution)?;
        let new_rhs = rhs.mul(cs, &rhs_contribution)?;

        lhs = Num::conditionally_select(cs, &can_pop, &new_lhs, &lhs)?;
        rhs = Num::conditionally_select(cs, &can_pop, &new_rhs, &rhs)?;
    }

    let (last_sk, last_k, (last_v0, last_v1)) = previous_key_value;

    Ok(((lhs, rhs), (last_sk, last_k, [last_v0, last_v1])))
}
