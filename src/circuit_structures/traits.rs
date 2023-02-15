use super::*;
use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;
use crate::traits::*;
use crate::vm::primitives::*;
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::rescue::PlonkCsSBox;
use franklin_crypto::rescue::*;
use rescue_poseidon::{
    circuit_generic_round_function, generic_round_function, CircuitGenericSponge, HashParams,
};
use std::convert::TryInto;
pub(crate) trait CircuitArithmeticEncodable<E: Engine>: Clone + Send + Sync {
    fn encoding_length_is_constant() -> bool {
        true
    }

    fn encoding_is_trivial() -> bool {
        false
    }

    fn encoding_length() -> usize;

    fn encoding_length_for_instance(&self) -> usize {
        if Self::encoding_length_is_constant() {
            Self::encoding_length()
        } else {
            unimplemented!()
        }
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError>;

    fn get_witness_value(&self) -> Option<Vec<E::Fr>> {
        None
    }
}

pub(crate) trait CircuitArithmeticEncodableExt<E: Engine>:
    CircuitArithmeticEncodable<E>
{
    type Witness: Clone + std::fmt::Debug;

    fn make_witness(&self) -> Option<Self::Witness>;
    fn placeholder_witness() -> Self::Witness;
}

pub(crate) trait CircuitArithmeticDecodable<E: Engine>: Clone + Send + Sync {
    fn parse<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
    ) -> Result<Self, SynthesisError>;
    fn parse_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        should_execute: &Boolean,
    ) -> Result<Self, SynthesisError>;
    // fn allocate_from_witness<CS: ConstraintSystem<E>>(cs: &mut CS, witness: Option<Vec<E::Fr>>) -> Result<Self, SynthesisError>;
}

pub(crate) trait CircuitArithmeticDecodableExt<E: Engine>:
    CircuitArithmeticEncodableExt<E>
{
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError>;
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError>;
}

use crate::vm::optimizer::sponge_set::*;

/// requires specialzied state, doesn't manage resets
pub fn raw_absorb_conditionally_using_optimizer<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    id: u64,
    execute: Boolean,
    state: [Num<E>; SWIDTH],
    input: [Num<E>; AWIDTH],
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<[Num<E>; SWIDTH], SynthesisError> {
    let initial_state_witness = Num::get_value_multiple(&state);
    let input_witness = Num::get_value_multiple(&input);

    let final_state_witness = match (initial_state_witness, input_witness) {
        (Some(initial_state_witness), Some(input_witness)) => {
            let final_state_witness = optimizer
                .round_function
                .simulate_absorb(initial_state_witness, &input_witness);

            Some(final_state_witness)
        }
        _ => None,
    };

    let mut provably_absorbed = state;
    for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(input.iter()) {
        *dst = dst.add(cs, src)?;
    }

    let final_state = Num::alloc_multiple::<_, SWIDTH>(cs, final_state_witness)?;

    let request = SpongeRoundRequest {
        initial_state: provably_absorbed,
        claimed_final_state: final_state,
    };

    optimizer.add_request(request, execute, id);

    Ok(final_state)
}

/// manage resets and specialization. Assumes reset on specialization
pub fn absorb_conditionally_using_optimizer_with_specializtion_and_reset<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    id: u64,
    execute: Boolean,
    state: [Num<E>; SWIDTH],
    input: [Num<E>; AWIDTH],
    specialize: Boolean,
    specialize_for_length: UInt16<E>,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<[Num<E>; SWIDTH], SynthesisError> {
    let specialized_state = optimizer
        .round_function
        .apply_length_specialization_for_variable(R::empty_state(), specialize_for_length);
    let state = <[Num<E>; SWIDTH] as CircuitSelectable<E>>::conditionally_select(
        cs,
        &specialize,
        &specialized_state,
        &state,
    )?;
    let initial_state_witness = Num::get_value_multiple(&state);
    let input_witness = Num::get_value_multiple(&input);

    let final_state_witness = match (initial_state_witness, input_witness) {
        (Some(initial_state_witness), Some(input_witness)) => {
            let final_state_witness = optimizer
                .round_function
                .simulate_absorb(initial_state_witness, &input_witness);

            Some(final_state_witness)
        }
        _ => None,
    };

    let final_state = Num::alloc_multiple::<_, SWIDTH>(cs, final_state_witness)?;

    let mut provably_absorbed = state;
    for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(input.iter()) {
        *dst = dst.add(cs, src)?;
    }

    let request = SpongeRoundRequest {
        initial_state: provably_absorbed,
        claimed_final_state: final_state,
    };

    optimizer.add_request(request, execute, id);

    Ok(final_state)
}

/// manage resets and specialization. Assumes reset on specialization
pub fn absorb_conditionally_using_optimizer_with_specializtion_and_reset_multiround<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    id: u64,
    execute: Boolean,
    state: [Num<E>; SWIDTH],
    input: &[Num<E>],
    specialize: Boolean,
    specialize_for_length: UInt16<E>,
    optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
) -> Result<[Num<E>; SWIDTH], SynthesisError> {
    assert!(input.len() % AWIDTH == 0);
    let specialized_state = optimizer
        .round_function
        .apply_length_specialization_for_variable(R::empty_state(), specialize_for_length);
    let mut state = <[Num<E>; SWIDTH] as CircuitSelectable<E>>::conditionally_select(
        cs,
        &specialize,
        &specialized_state,
        &state,
    )?;
    let _last_round_idx = (input.len() / AWIDTH) - 1;

    for (_round_idx, round_input) in input.chunks(AWIDTH).enumerate() {
        let initial_state_witness = Num::get_value_multiple(&state);
        use std::convert::TryInto;

        let values_to_absorb: [Num<E>; AWIDTH] = round_input.try_into().expect("length must match");
        let input_witness = Num::get_value_multiple(&values_to_absorb);

        let final_state_witness = match (initial_state_witness, input_witness) {
            (Some(initial_state_witness), Some(input_witness)) => {
                let final_state_witness = optimizer
                    .round_function
                    .simulate_absorb(initial_state_witness, &input_witness);

                Some(final_state_witness)
            }
            _ => None,
        };

        let mut provably_absorbed = state;
        for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(input.iter()) {
            *dst = dst.add(cs, src)?;
        }

        let final_state = Num::alloc_multiple::<_, SWIDTH>(cs, final_state_witness)?;

        let request = SpongeRoundRequest {
            initial_state: provably_absorbed,
            claimed_final_state: final_state,
        };

        optimizer.add_request(request, execute, id);

        state = final_state;
    }

    Ok(state)
}

// default implementation for Num<E>

impl<E: Engine> CircuitArithmeticEncodable<E> for Num<E> {
    fn encoding_length() -> usize {
        1
    }

    fn encoding_is_trivial() -> bool {
        true
    }

    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        Ok(vec![self.clone()])
    }

    fn get_witness_value(&self) -> Option<Vec<E::Fr>> {
        if let Some(wit) = self.get_value() {
            return Some(vec![wit]);
        } else {
            return None;
        }
    }
}

impl<E: Engine> CircuitArithmeticDecodable<E> for Num<E> {
    fn parse<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>],
    ) -> Result<Self, SynthesisError> {
        assert_eq!(values.len(), 1);

        Ok(values[0])
    }
    fn parse_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        should_execute: &Boolean,
    ) -> Result<Self, SynthesisError> {
        // return 0
        assert_eq!(values.len(), 1);

        let candidate = values[0];

        Num::conditionally_select(
            cs,
            &should_execute,
            &candidate,
            &Num::Constant(E::Fr::zero()),
        )
    }
}

// impl<E: Engine> CircuitArithmeticCommitable<E> for Num<E> {}

// default implementation for [Num<E>; N]

impl<E: Engine, const N: usize> CircuitArithmeticEncodable<E> for [Num<E>; N] {
    fn encoding_length() -> usize {
        N
    }

    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut result = Vec::with_capacity(N);
        result.extend_from_slice(&self[..]);

        Ok(result)
    }

    fn get_witness_value(&self) -> Option<Vec<E::Fr>> {
        let mut result = Vec::with_capacity(N);
        for el in self.iter() {
            if let Some(wit) = el.get_value() {
                result.push(wit);
            } else {
                return None;
            }
        }

        Some(result)
    }
}

impl<E: Engine, const N: usize> CircuitArithmeticDecodable<E> for [Num<E>; N] {
    fn parse<CS: ConstraintSystem<E>>(
        _cs: &mut CS,
        values: &[Num<E>],
    ) -> Result<Self, SynthesisError> {
        assert_eq!(values.len(), N);

        let mut new = [Num::Constant(E::Fr::zero()); N];
        for (el, val) in new.iter_mut().zip(values.iter()) {
            *el = val.clone();
        }

        Ok(new)
    }
    fn parse_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        should_execute: &Boolean,
    ) -> Result<Self, SynthesisError> {
        // return 0
        assert_eq!(values.len(), N);

        let mut new = [Num::Constant(E::Fr::zero()); N];
        for (el, val) in new.iter_mut().zip(values.iter()) {
            *el = Num::conditionally_select(cs, &should_execute, &val, &el)?;
            *el = val.clone();
        }

        Ok(new)
    }
}

use franklin_crypto::plonk::circuit::byte::*;

impl<E: Engine> CircuitArithmeticEncodable<E> for Byte<E> {
    fn encoding_length() -> usize {
        1
    }

    fn encoding_is_trivial() -> bool {
        true
    }

    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let result = vec![self.inner];
        Ok(result)
    }

    fn get_witness_value(&self) -> Option<Vec<E::Fr>> {
        let mut result = Vec::with_capacity(1);
        if let Some(wit) = self.inner.get_value() {
            result.push(wit);
        } else {
            return None;
        }

        Some(result)
    }
}

impl<E: Engine> CircuitArithmeticEncodableExt<E> for Byte<E> {
    type Witness = u8;

    fn make_witness(&self) -> Option<Self::Witness> {
        self.get_byte_value()
    }

    fn placeholder_witness() -> Self::Witness {
        0u8
    }
}

impl<E: Engine> CircuitArithmeticDecodableExt<E> for Byte<E> {
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            values.len(),
            <Self as CircuitArithmeticEncodable<E>>::encoding_length()
        );

        let new = Byte::from_u8_witness(cs, witness)?;
        let encoding = <Self as CircuitArithmeticEncodable<E>>::encode(&new, cs)?;

        for (enc, val) in encoding.into_iter().zip(values.iter()) {
            enc.enforce_equal(cs, val)?;
        }

        Ok(new)
    }

    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(
            values.len(),
            <Self as CircuitArithmeticEncodable<E>>::encoding_length()
        );

        let new = Byte::from_u8_witness(cs, witness)?;
        let encoding = <Self as CircuitArithmeticEncodable<E>>::encode(&new, cs)?;

        let eq = Num::equals(cs, &encoding[0], &values[0])?;

        use super::utils::*;

        can_not_be_false_if_flagged(cs, &eq, should_execute)?;

        Ok(new)
    }
}

// impl<E: Engine> CircuitArithmeticCommitable<E> for Byte<E> {}

use crate::vm::structural_eq::*;

pub trait CircuitArithmeticRoundFunction<E: Engine, const AWIDTH: usize, const SWIDTH: usize>:
    Clone + Eq
{
    type StateElement: Clone + CircuitEq<E> + CircuitSelectable<E>;

    fn simulate_round_function(&self, state: [E::Fr; SWIDTH]) -> [E::Fr; SWIDTH];

    fn simulate_absorb(&self, state: [E::Fr; SWIDTH], input: &[E::Fr]) -> [E::Fr; SWIDTH] {
        assert!(input.len() < SWIDTH);
        let mut state = state;
        for (s, inp) in state.iter_mut().zip(input.iter()) {
            s.add_assign(inp);
        }

        self.simulate_round_function(state)
    }

    fn simulate_absorb_into_empty_with_specialization(&self, input: &[E::Fr]) -> [E::Fr; SWIDTH] {
        let input_length = input.len();
        let state =
            self.simulate_apply_length_specialization(self.simulate_empty_state(), input_length);
        self.simulate_absorb(state, input)
    }

    fn simulate_absorb_multiple_rounds(
        &self,
        state: [E::Fr; SWIDTH],
        input: &[E::Fr],
    ) -> Vec<([E::Fr; SWIDTH], [E::Fr; SWIDTH])>;

    fn num_absorbtion_rounds_for_input_length(&self, length: usize) -> usize;

    fn simulate_absorb_multiple_rounds_into_empty_with_specialization(
        &self,
        input: &[E::Fr],
    ) -> Vec<([E::Fr; SWIDTH], [E::Fr; SWIDTH])> {
        let input_length = input.len();
        let state =
            self.simulate_apply_length_specialization(self.simulate_empty_state(), input_length);
        self.simulate_absorb_multiple_rounds(state, input)
    }

    fn simulate_empty_state(&self) -> [E::Fr; SWIDTH] {
        [E::Fr::zero(); SWIDTH]
    }

    fn empty_state() -> [Self::StateElement; SWIDTH];

    #[track_caller]
    fn simulate_apply_length_specialization(
        &self,
        state: [E::Fr; SWIDTH],
        _length: usize,
    ) -> [E::Fr; SWIDTH] {
        assert!(state == self.simulate_empty_state());
        unimplemented!();
    }

    #[track_caller]
    fn apply_length_specialization(
        &self,
        state: [Self::StateElement; SWIDTH],
        _length: usize,
    ) -> [Self::StateElement; SWIDTH] {
        assert!(state.eq(&Self::empty_state()));
        unimplemented!();
    }

    #[track_caller]
    fn apply_length_specialization_for_variable(
        &self,
        state: [Self::StateElement; SWIDTH],
        _length: UInt16<E>,
    ) -> [Self::StateElement; SWIDTH] {
        assert!(state.eq(&Self::empty_state()));
        unimplemented!();
    }

    fn round_function<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        state: [Self::StateElement; SWIDTH],
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError>;

    fn round_function_absorb_nums<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        state: [Self::StateElement; SWIDTH],
        input: &[Num<E>],
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError>;

    fn round_function_absorb_nums_multiple_rounds<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        state: [Self::StateElement; SWIDTH],
        input: &[Num<E>],
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError> {
        assert!(input.len() % AWIDTH == 0);
        let mut state = state;
        for chunk in input.chunks_exact(AWIDTH) {
            state = self.round_function_absorb_nums(cs, state, chunk)?
        }

        Ok(state)
    }

    // fn round_function_absorb_lcs<CS: ConstraintSystem<E>, const N: usize>(
    //     &self, cs: &mut CS, state: [Self::StateElement; N], input: &[LinearCombination<E>]
    // ) -> Result<[Self::StateElement; N], SynthesisError>;

    fn state_into_commitment(state: [Self::StateElement; SWIDTH])
        -> Result<Num<E>, SynthesisError>;

    fn simulate_state_into_commitment(state: [E::Fr; SWIDTH]) -> E::Fr;

    fn chunk_and_pad_input(&self, input: &[Num<E>]) -> Vec<Vec<Num<E>>>;
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH> for GenericHasher<E, P, AWIDTH, SWIDTH>
{
    type StateElement = Num<E>;

    fn simulate_round_function(&self, state: [E::Fr; SWIDTH]) -> [E::Fr; SWIDTH] {
        let mut new_state = state;

        generic_round_function(&self.params, &mut new_state);

        new_state
    }

    fn num_absorbtion_rounds_for_input_length(&self, length: usize) -> usize {
        let mut num_rounds = length / AWIDTH;
        if length % AWIDTH != 0 {
            num_rounds += 1;
        }

        num_rounds
    }

    fn simulate_absorb_multiple_rounds(
        &self,
        state: [E::Fr; SWIDTH],
        input: &[E::Fr],
    ) -> Vec<([E::Fr; SWIDTH], [E::Fr; SWIDTH])> {
        let padding = E::Fr::one();
        let length = input.len();
        let rate = AWIDTH;
        let num_rounds = self.num_absorbtion_rounds_for_input_length(length);

        let pad_by = rate - length % rate;
        let mut it = input.iter().chain(std::iter::repeat(&padding).take(pad_by));
        let mut state = state;

        let mut round_outputs = Vec::with_capacity(num_rounds);

        let iterable = &mut it;
        for _ in 0..num_rounds {
            for (s, inp) in state.iter_mut().zip(iterable.take(rate)) {
                s.add_assign(inp);
            }
            let initial_state = state;
            state = self.simulate_round_function(state);
            round_outputs.push((initial_state, state));
        }

        round_outputs
    }

    #[track_caller]
    fn simulate_apply_length_specialization(
        &self,
        state: [E::Fr; SWIDTH],
        length: usize,
    ) -> [E::Fr; SWIDTH] {
        assert!(state == self.simulate_empty_state());
        let mut state = state;
        let idx = state.len() - 1;
        state[idx] = u64_to_fe(length as u64);

        state
    }

    fn empty_state() -> [Self::StateElement; SWIDTH] {
        [Num::zero(); SWIDTH]
    }

    fn apply_length_specialization(
        &self,
        state: [Self::StateElement; SWIDTH],
        length: usize,
    ) -> [Self::StateElement; SWIDTH] {
        assert!(state.eq(&Self::empty_state()));

        let mut state = state;
        *state.last_mut().expect("is some") = Num::Constant(u64_to_fe(length as u64));

        state
    }

    fn apply_length_specialization_for_variable(
        &self,
        state: [Self::StateElement; SWIDTH],
        length: UInt16<E>,
    ) -> [Self::StateElement; SWIDTH] {
        assert!(state.eq(&Self::empty_state()));

        let mut state = state;
        *state.last_mut().expect("is some") = length.inner;

        state
    }

    fn round_function<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        state: [Self::StateElement; SWIDTH],
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError> {
        let mut state_lcs = arrayvec::ArrayVec::<_, SWIDTH>::new();
        for s in state.iter() {
            let lc = LinearCombination::from(*s);
            state_lcs.push(lc);
        }
        let mut state_lcs = state_lcs.into_inner().expect("length must match");

        circuit_generic_round_function(cs, &mut state_lcs, &self.params)?;

        let mut new_state = [Num::Constant(E::Fr::zero()); SWIDTH];
        for (a, b) in new_state.iter_mut().zip(state_lcs.into_iter()) {
            *a = b.into_num(cs)?;
        }

        Ok(new_state)
    }

    fn round_function_absorb_nums<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        state: [Self::StateElement; SWIDTH],
        input: &[Num<E>],
    ) -> Result<[Self::StateElement; SWIDTH], SynthesisError> {
        assert_eq!(input.len(), AWIDTH);
        use franklin_crypto::plonk::circuit::rescue::StatefulRescueGadget;

        let mut state_lcs = arrayvec::ArrayVec::<_, SWIDTH>::new();
        for (s, inp) in state[..input.len()].iter().zip(input.iter()) {
            let mut lc = LinearCombination::from(*s);
            lc.add_assign_number_with_coeff(&inp, E::Fr::one());
            state_lcs.push(lc);
        }

        for s in state[input.len()..].iter() {
            let lc = LinearCombination::from(*s);
            state_lcs.push(lc);
        }

        let mut state_lcs = state_lcs.into_inner().expect("length must match");

        circuit_generic_round_function(cs, &mut state_lcs, &self.params)?;

        let mut new_state = [Num::Constant(E::Fr::zero()); SWIDTH];
        for (a, b) in new_state.iter_mut().zip(state_lcs.into_iter()) {
            *a = b.into_num(cs)?;
        }

        Ok(new_state)
    }

    // fn round_function_absorb_lcs<CS: ConstraintSystem<E>, const N: usize>(
    //     cs: &mut CS, state: [Self::StateElement; N], input: &[LinearCombination<E>]
    // ) -> Result<[Self::StateElement; N], SynthesisError>;

    fn state_into_commitment(
        state: [Self::StateElement; SWIDTH],
    ) -> Result<Num<E>, SynthesisError> {
        Ok(state[0])
    }

    fn simulate_state_into_commitment(state: [E::Fr; SWIDTH]) -> E::Fr {
        state[0]
    }

    fn chunk_and_pad_input(&self, input: &[Num<E>]) -> Vec<Vec<Num<E>>> {
        let num_rounds = self.num_absorbtion_rounds_for_input_length(input.len());
        let mut result = Vec::with_capacity(num_rounds);
        let rate = AWIDTH;
        let mut chunks_it = input.chunks(rate);
        for _ in 0..num_rounds {
            let mut chunk = chunks_it.next().expect("is some").to_vec();
            chunk.resize(rate, Num::Constant(E::Fr::one()));
            result.push(chunk);
        }

        result
    }
}
