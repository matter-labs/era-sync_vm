use super::*;

pub fn simulate_variable_length_hash<
    E: Engine,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    input: &[E::Fr],
    round_function: &R,
) -> E::Fr {
    let mut sequence_of_simulated_states =
        round_function.simulate_absorb_multiple_rounds_into_empty_with_specialization(input);
    let state = sequence_of_simulated_states.pop().expect("is some").1;
    let committment = R::simulate_state_into_commitment(state);

    committment
}

pub fn simulate_variable_length_absorb_into_state<
    E: Engine,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    input: &[E::Fr],
    into_state: &[E::Fr; SWIDTH],
    round_function: &R,
) -> Result<[E::Fr; SWIDTH], SynthesisError> {
    let mut state = *into_state;
    for chunk in input.chunks(AWIDTH) {
        let padding_els = AWIDTH - chunk.len();
        let input_fixed_len: [E::Fr; AWIDTH] = if padding_els == 0 {
            chunk.try_into().expect("length must match")
        } else {
            let tmp = E::Fr::one();
            let it = chunk
                .iter()
                .chain(std::iter::repeat(&tmp).take(padding_els));

            it.copied()
                .collect::<Vec<_>>()
                .as_slice()
                .try_into()
                .expect("length must match")
        };

        state = round_function.simulate_absorb(state, &input_fixed_len);
    }

    Ok(state)
}

pub fn simulate_variable_length_hash_with_rescue_prime_padding<
    E: Engine,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    input: &[E::Fr],
    round_function: &R,
) -> Result<E::Fr, SynthesisError> {
    let len_residue = input.len() % AWIDTH;
    let one = E::Fr::one();
    let zero = E::Fr::zero();

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

    let state = round_function.simulate_empty_state();
    let state =
        simulate_variable_length_absorb_into_state(&padded_input[..], &state, round_function)?;

    let commitment = R::simulate_state_into_commitment(state);

    Ok(commitment)
}
