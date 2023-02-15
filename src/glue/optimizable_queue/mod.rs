use super::*;

pub mod queue_pusher;
pub mod simple_impl;
pub mod simulate_hash;
pub mod witness_queue;

pub use self::queue_pusher::*;
pub use self::simple_impl::*;
pub use self::simulate_hash::*;

use super::traits::*;
use crate::vm::optimizer::sponge_set::*;
use std::convert::TryInto;

/// NOTE: "variable length" here only means that we accept a slice and not a fixed length array as an input.
/// Caller ideally should use fixed length functions to ensure additional invariants if he can

pub fn variable_length_hash_using_optimizer_for_item<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodable<E, N>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &I,
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<Num<E>, SynthesisError> {
    let input = input.encode(cs)?;
    variable_length_hash_using_optimizer(cs, &input[..], id, execute, optimizer)
}

pub fn fixed_width_hash<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<E>; N],
    round_function: &R,
) -> Result<Num<E>, SynthesisError> {
    variable_length_hash(cs, &input[..], round_function)
}

pub fn fixed_width_hash_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<E>; N],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<Num<E>, SynthesisError> {
    let state =
        fixed_width_hash_into_empty_state_using_optimizer(cs, input, id, execute, optimizer)?;

    let committment = R::state_into_commitment(state)?;

    Ok(committment)
}

pub fn variable_length_hash<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    round_function: &R,
) -> Result<Num<E>, SynthesisError> {
    let state = variable_length_absorb_into_empty_state(cs, input, round_function)?;

    let committment = R::state_into_commitment(state)?;

    Ok(committment)
}

pub fn variable_length_hash_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<Num<E>, SynthesisError> {
    let state =
        variable_length_hash_into_empty_state_using_optimizer(cs, input, id, execute, optimizer)?;

    let committment = R::state_into_commitment(state)?;

    Ok(committment)
}

pub fn fixed_width_hash_into_empty_state_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<E>; N],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    assert!(N % AWIDTH == 0);
    variable_length_hash_into_empty_state_using_optimizer(cs, input, id, execute, optimizer)
}

pub fn variable_length_hash_into_empty_state_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    let empty_state = R::empty_state();
    let len = input.len();
    let specialized_state = optimizer
        .round_function
        .apply_length_specialization(empty_state, len);

    variable_length_absorb_into_state_using_optimizer(
        cs,
        input,
        &specialized_state,
        id,
        execute,
        optimizer,
    )
}

pub fn fixed_width_hash_into_state_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<E>; N],
    into_state: &[R::StateElement; SWIDTH],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    assert!(N % AWIDTH == 0);

    variable_length_absorb_into_state_using_optimizer(cs, input, into_state, id, execute, optimizer)
}

pub fn variable_length_absorb_into_state_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    into_state: &[R::StateElement; SWIDTH],
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    let len = input.len();
    let input_witness = Num::get_value_for_slice(&input);
    let state_witness = Num::get_value_multiple(&into_state);

    let num_rounds = optimizer
        .round_function
        .num_absorbtion_rounds_for_input_length(len);

    let intermediate_states = match (input_witness, state_witness, execute.get_value()) {
        (Some(input_witness), Some(state_witness), Some(execute)) => {
            if execute {
                let intemediates = optimizer
                    .round_function
                    .simulate_absorb_multiple_rounds(state_witness, &input_witness[..]);

                Some(intemediates)
            } else {
                // we still need some dummy witness

                let dummy_witness =
                    vec![([E::Fr::zero(); SWIDTH], [E::Fr::zero(); SWIDTH]); num_rounds];

                Some(dummy_witness)
            }
        }
        _ => None,
    };

    let input_chunks = optimizer.round_function.chunk_and_pad_input(input);

    let mut last_state = *into_state;
    assert_eq!(input_chunks.len(), num_rounds);

    for round_id in 0..num_rounds {
        let witness = intermediate_states.as_ref().map(|el| el[round_id].1);
        let intermediate = Num::alloc_multiple(cs, witness)?;

        let chunk = &input_chunks[round_id][..];

        let padding_els = AWIDTH - chunk.len();
        let input_fixed_len: [Num<E>; AWIDTH] = if padding_els == 0 {
            chunk.try_into().expect("length must match")
        } else {
            let tmp = Num::one();
            let it = chunk
                .iter()
                .chain(std::iter::repeat(&tmp).take(padding_els));

            it.copied()
                .collect::<Vec<_>>()
                .as_slice()
                .try_into()
                .expect("length must match")
        };

        let mut provably_absorbed = last_state;

        // absorb by addition
        for (dst, src) in provably_absorbed[..AWIDTH]
            .iter_mut()
            .zip(input_fixed_len.iter())
        {
            if dst.is_constant() {
                if dst.get_constant_value() == E::Fr::zero() {
                    // just copy
                    *dst = *src;
                }
            } else {
                *dst = dst.add(cs, src)?;
            }
        }

        let request = SpongeRoundRequest {
            initial_state: provably_absorbed,
            claimed_final_state: intermediate,
        };

        optimizer.add_request(request, execute, id);

        last_state = intermediate;
    }

    Ok(last_state)
}

pub fn fixed_width_absorb_into_state<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<E>; N],
    into_state: &[R::StateElement; SWIDTH],
    round_function: &R,
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    variable_length_absorb_into_state::<_, _, _, AWIDTH, SWIDTH>(
        cs,
        &input[..],
        into_state,
        round_function,
    )
}

pub fn variable_length_absorb_into_state<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    into_state: &[R::StateElement; SWIDTH],
    round_function: &R,
) -> Result<[R::StateElement; SWIDTH], SynthesisError> {
    let mut state = *into_state;
    for chunk in input.chunks(AWIDTH) {
        let padding_els = AWIDTH - chunk.len();
        let input_fixed_len: [Num<E>; AWIDTH] = if padding_els == 0 {
            chunk.try_into().expect("length must match")
        } else {
            let tmp = Num::one();
            let it = chunk
                .iter()
                .chain(std::iter::repeat(&tmp).take(padding_els));

            it.copied()
                .collect::<Vec<_>>()
                .as_slice()
                .try_into()
                .expect("length must match")
        };

        state = round_function.round_function_absorb_nums(cs, state, &input_fixed_len)?;
    }

    Ok(state)
}

pub fn variable_length_absorb_into_empty_state<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    round_function: &R,
) -> Result<[Num<E>; SWIDTH], SynthesisError> {
    let state = R::empty_state();
    let state = round_function.apply_length_specialization(state, input.len());
    let state = variable_length_absorb_into_state(cs, &input[..], &state, round_function)?;

    Ok(state)
}

pub fn fixed_length_absorb_into_empty_state<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<E>; N],
    round_function: &R,
) -> Result<[Num<E>; SWIDTH], SynthesisError> {
    variable_length_absorb_into_empty_state::<_, _, _, AWIDTH, SWIDTH>(
        cs,
        &input[..],
        round_function,
    )
}

pub fn commit_encodable_item_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodable<E, N>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    item: &I,
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<Num<E>, SynthesisError> {
    variable_length_hash_using_optimizer_for_item(cs, item, id, execute, optimizer)
}

pub fn commit_encodable_item<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodable<E, N>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    item: &I,
    round_function: &R,
) -> Result<Num<E>, SynthesisError> {
    let input = item.encode(cs)?;
    fixed_width_hash(cs, &input, round_function)
}

pub fn commit_variable_length_encodable_item<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitVariableLengthEncodable<E>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    item: &I,
    round_function: &R,
) -> Result<Num<E>, SynthesisError> {
    let input = item.encode(cs)?;
    variable_length_hash(cs, &input, round_function)
}

pub fn decommit_encodable_item<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    witness: Option<I::Witness>,
    commitment: Num<E>,
    round_function: &R,
) -> Result<I, SynthesisError> {
    let item = I::allocate_from_witness(cs, witness)?;
    let recomputed_commitment = commit_encodable_item(cs, &item, round_function)?;
    commitment.enforce_equal(cs, &recomputed_commitment)?;

    Ok(item)
}

pub fn decommit_encodable_item_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    witness: Option<I::Witness>,
    commitment: Num<E>,
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<I, SynthesisError> {
    let item = I::allocate_from_witness(cs, witness)?;
    let recomputed_commitment =
        commit_encodable_item_using_optimizer(cs, &item, id, execute, optimizer)?;
    commitment.enforce_equal(cs, &recomputed_commitment)?;

    Ok(item)
}

pub fn conditionally_decommit_encodable_item<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    witness: Option<I::Witness>,
    commitment: Num<E>,
    must_be_valid: Boolean,
    round_function: &R,
) -> Result<I, SynthesisError> {
    let item = I::allocate_from_witness(cs, witness)?;
    let recomputed_commitment = commit_encodable_item(cs, &item, round_function)?;
    let equals = Num::equals(cs, &commitment, &recomputed_commitment)?;
    can_not_be_false_if_flagged(cs, &equals, &must_be_valid)?;

    Ok(item)
}

pub fn conditionally_decommit_encodable_item_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const AWIDTH: usize,
    const SWIDTH: usize,
    const N: usize,
>(
    cs: &mut CS,
    witness: Option<I::Witness>,
    commitment: Num<E>,
    must_be_valid: Boolean,
    id: u64,
    execute: Boolean,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<I, SynthesisError> {
    let item = I::allocate_from_witness(cs, witness)?;
    let recomputed_commitment =
        commit_encodable_item_using_optimizer(cs, &item, id, execute, optimizer)?;
    let equals = Num::equals(cs, &commitment, &recomputed_commitment)?;
    let must_be_valid = Boolean::and(cs, &must_be_valid, &execute)?;
    can_not_be_false_if_flagged(cs, &equals, &must_be_valid)?;

    Ok(item)
}

pub fn variable_length_hash_with_rescue_prime_padding<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    input: &[Num<E>],
    round_function: &R,
) -> Result<Num<E>, SynthesisError> {
    // we do not apply length specialization and instead do the padding
    let len_residue = input.len() % AWIDTH;
    let one = Num::one();
    let zero = Num::zero();

    let padded_input = if len_residue == AWIDTH - 1 {
        let it = input.iter().chain(std::iter::once(&one));
        let padded_input: Vec<_> = it.copied().collect();

        padded_input
    } else {
        let repeat = AWIDTH - len_residue - 1;
        let it = input
            .iter()
            .chain(std::iter::once(&one))
            .chain(std::iter::repeat(&zero).take(repeat));
        let padded_input: Vec<_> = it.copied().collect();

        padded_input
    };

    let state = R::empty_state();
    let state = variable_length_absorb_into_state(cs, &padded_input[..], &state, round_function)?;

    let commitment = R::state_into_commitment(state)?;

    Ok(commitment)
}
