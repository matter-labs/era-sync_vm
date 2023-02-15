use super::*;

pub fn partial_accumulate_inner<
    E: Engine, 
    CS: ConstraintSystem<E>, 
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>
>(
    cs: &mut CS,
    unsorted_queue: &mut DecommitmentRequestsQueue::<E, 2, 3>,
    sorted_queuee: &mut DecommitmentRequestsQueue::<E, 2, 3>,
    result_queue: &mut DelegatedMemoryWritesQueue<E, 2, 3>,
    fs_challenges: &[Num<E>; 3],
    initial_lhs: Num<E>,
    initial_rhs: Num<E>,
    continue_argument: Boolean,
    previous_full_key: UInt32<E>,
    last_element_value: Num<E>,
    round_function: &R,
    limit: usize
) -> Result<((Num<E>, Num<E>), (UInt32<E>, Num<E>)), SynthesisError> {
    // we only need to prove that into any memory page we decommit a unique hash
    // even if the operator decommits same hash to different pages it's ok since it only makes proving
    // more difficult
    assert!(limit <= u32::MAX as usize);
    let mut lhs = initial_lhs;
    let mut rhs = initial_rhs;

    let [challenge_0, challenge_1, additive_part] = *fs_challenges;

    let v0 = last_element_value;
    let mut previous_key_value = (previous_full_key, v0);

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
            let (previous_sk, previous_v0) = previous_key_value;
            let sk = sorted_item.memory_page;
            let v0 = sorted_item.hash;

            // ensure sorting
            let (keys_are_equal, previous_key_is_greater) = prepacked_long_comparison(
                cs, 
                &[previous_sk.inner],
                &[sk.inner],
                &[32]
            )?;
            let keys_are_in_ascending_order = smart_and(cs, &[previous_key_is_greater.not(), keys_are_equal.not()])?;
            if _cycle != 0 {
                can_not_be_false_if_flagged(cs, &keys_are_in_ascending_order, &can_pop)?;
            } else {
                let should_enforce = smart_and(cs, &[can_pop, continue_argument])?;
                can_not_be_false_if_flagged(cs, &keys_are_in_ascending_order, &should_enforce)?;
            }
            
            let same_memory_cell = keys_are_equal;
            let v0_equal = Num::equals(cs, &previous_v0, &v0)?;

            if _cycle != 0 {
                let value_equal = v0_equal;
                let check_equality = same_memory_cell;
                can_not_be_false_if_flagged(cs, &value_equal, &check_equality)?;
                let first_for_new_cell = smart_and(cs, &[same_memory_cell.not(), can_pop])?;
                Boolean::enforce_equal(cs, &sorted_item.is_first, &first_for_new_cell)?;

                let push = first_for_new_cell;
                let item = DelegatedMemoryWriteRecord {
                    memory_page: sorted_item.memory_page,
                    hash: sorted_item.hash,
                };
                result_queue.push(cs, &item, &push, round_function)?;
            } else {
                let check_equality = smart_and(cs, &[can_pop, continue_argument.not()])?;
                can_not_be_false_if_flagged(cs, &sorted_item.is_first, &check_equality)?;
                
                let push = sorted_item.is_first;
                let item = DelegatedMemoryWriteRecord {
                    memory_page: sorted_item.memory_page,
                    hash: sorted_item.hash,
                };
                result_queue.push(cs, &item, &push, round_function)?;
            }

            let push = smart_and(cs, &[same_memory_cell.not(), can_pop])?;

            previous_key_value = (sk, v0);
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

    let (last_sk, last_v0) = previous_key_value;

    Ok(((lhs, rhs), (last_sk, last_v0)))
}

fn calculate_permutation<E: Engine>(els: &Vec<DecommitmentRequest<E>>) -> Option<IntegerPermutation> {
    // we have to sort it based on the index, then PC

    let mut keys = vec![];
    for el in els.iter() {
        if let Some(wit) = el.create_witness() {
            let composite_key: BigUint = (BigUint::from(wit.memory_page as u64) << 1) + BigUint::from(wit.is_first as u64);
            let idx = keys.len();
            keys.push((idx, composite_key));
        } else {
            return None
        }
    }

    // we have all the keys, so let's sort it
    // based on the composite key, and get indexes for free
    keys.sort_by(|a, b| a.1.cmp(&b.1));
    let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();

    let integer_permutation = IntegerPermutation::new_from_permutation(integer_permutation);

    Some(integer_permutation)
}