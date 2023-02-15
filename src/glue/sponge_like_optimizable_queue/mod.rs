use super::super::traits::*;
use super::optimizable_queue::*;
use super::traits::*;
use super::*;
use crate::bellman::SynthesisError;
use crate::circuit_structures::traits::*;
use crate::derivative::*;
use crate::ff::*;
use crate::vm::optimizer::sponge_set::*;
use crate::ConstraintSystem;
use crate::{pairing::*, vm::primitives::UInt16};
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::Assignment;
use franklin_crypto::rescue::*;
use serde::ser::SerializeStruct;
use std::collections::VecDeque;
use std::convert::TryInto;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
pub struct FixedWidthEncodingSpongeLikeQueueWitness<
    E: Engine,
    I: CircuitFixedLengthEncodableExt<E, N>,
    const N: usize,
    const SWIDTH: usize,
> {
    #[serde(bound(
        serialize = "[E::Fr; N]: serde::Serialize, [E::Fr; SWIDTH]: serde::Serialize, <I as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "[E::Fr; N]: serde::de::DeserializeOwned, [E::Fr; SWIDTH]: serde::de::DeserializeOwned, <I as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub wit: VecDeque<(
        [E::Fr; N],
        <I as CSWitnessable<E>>::Witness,
        [E::Fr; SWIDTH],
    )>,
}

impl<E: Engine, I: CircuitFixedLengthEncodableExt<E, N>, const N: usize, const SWIDTH: usize>
    CircuitEmpty<E> for FixedWidthEncodingSpongeLikeQueueWitness<E, I, N, SWIDTH>
{
    fn empty() -> Self {
        Self {
            wit: VecDeque::new(),
        }
    }
}

impl<E: Engine, I: CircuitFixedLengthEncodableExt<E, N>, const N: usize, const SWIDTH: usize>
    FixedWidthEncodingSpongeLikeQueueWitness<E, I, N, SWIDTH>
{
    pub(crate) fn pop_first(&mut self) -> ([E::Fr; N], <I as CSWitnessable<E>>::Witness) {
        let (encoding, witness, _) = self
            .wit
            .pop_front()
            .expect("must have enough witness items");

        (encoding, witness)
    }

    pub(crate) fn push(
        &mut self,
        new_item_encoding: [E::Fr; N],
        new_item_witness: <I as CSWitnessable<E>>::Witness,
        previous_tail: [E::Fr; SWIDTH],
    ) {
        self.wit
            .push_back((new_item_encoding, new_item_witness, previous_tail));
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.wit.is_empty()
    }

    pub(crate) fn some_split_hint(
        &self,
        at: Option<usize>,
    ) -> (Option<[E::Fr; SWIDTH]>, Option<bool>) {
        if let Some(at) = at {
            let (intermediate, non_trivial) = self.split_hint(at);
            (Some(intermediate), Some(non_trivial))
        } else {
            (None, None)
        }
    }

    pub(crate) fn split_hint(&self, at: usize) -> ([E::Fr; SWIDTH], bool) {
        if self.wit.len() <= at {
            return ([E::Fr::zero(); SWIDTH], false);
        } else {
            let (_, _, tail) = &self.wit[at];
            return (*tail, true);
        }
    }

    pub(crate) fn split(self, at: usize) -> (Self, Self) {
        if self.wit.len() <= at {
            let first = self;
            let second = Self::empty();

            (first, second)
        } else {
            todo!()
        }
    }

    pub(crate) fn some_split(self, at: Option<usize>) -> (Self, Self) {
        if let Some(at) = at {
            self.split(at)
        } else {
            (Self::empty(), Self::empty())
        }
    }
}

// this queue is implemented not as
// state = hash(state, item)
// but as state = absorb(state, item)

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct FixedWidthEncodingSpongeLikeQueue<
    E: Engine,
    I: CircuitFixedLengthEncodableExt<E, N>,
    const N: usize,
    const AWIDTH: usize,
    const SWIDTH: usize,
> {
    pub(crate) num_items: UInt32<E>,
    pub(crate) head_state: [Num<E>; SWIDTH],
    pub(crate) tail_state: [Num<E>; SWIDTH],
    #[derivative(Debug = "ignore")]
    pub(crate) witness: FixedWidthEncodingSpongeLikeQueueWitness<E, I, N, SWIDTH>,
}

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
        const AWIDTH: usize,
        const SWIDTH: usize,
    > FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>
{
    pub fn empty() -> Self {
        let zero = Num::zero();
        Self {
            num_items: UInt32::zero(),
            head_state: [zero; SWIDTH],
            tail_state: [zero; SWIDTH],
            witness: FixedWidthEncodingSpongeLikeQueueWitness::<E, I, N, SWIDTH>::empty(),
        }
    }

    pub fn from_raw_parts<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        head: [Num<E>; SWIDTH],
        tail: [Num<E>; SWIDTH],
        length: UInt32<E>,
    ) -> Result<Self, SynthesisError> {
        let length_is_zero = length.is_zero(cs)?;
        let mut tmp = vec![];
        for (h, t) in head.iter().zip(tail.iter()) {
            let e = Num::equals(cs, &h, &t)?;
            tmp.push(e);
        }
        let head_is_equal_to_tail = smart_and(cs, &tmp)?;
        Boolean::enforce_equal(cs, &length_is_zero, &head_is_equal_to_tail)?;

        let new = Self {
            num_items: length,
            head_state: head,
            tail_state: tail,
            witness: FixedWidthEncodingSpongeLikeQueueWitness::<E, I, N, SWIDTH>::empty(),
        };

        Ok(new)
    }

    pub fn from_tail_and_length<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        tail: [Num<E>; SWIDTH],
        length: UInt32<E>,
    ) -> Result<Self, SynthesisError> {
        let length_is_zero = length.is_zero(cs)?;
        let mut tmp = vec![];
        for t in tail.iter() {
            let e = t.is_zero(cs)?;
            tmp.push(e);
        }
        let tail_is_zero = smart_and(cs, &tmp)?;
        Boolean::enforce_equal(cs, &length_is_zero, &tail_is_zero)?;

        let new = Self {
            num_items: length,
            head_state: [Num::zero(); SWIDTH],
            tail_state: tail,
            witness: FixedWidthEncodingSpongeLikeQueueWitness::<E, I, N, SWIDTH>::empty(),
        };

        Ok(new)
    }

    #[track_caller]
    pub fn push_with_optimizer<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        id: u64,
        value: &I,
        execute: &Boolean,
        optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
    ) -> Result<(), SynthesisError> {
        assert!(N % AWIDTH == 0);

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;
        let value_encoding = value.encode(cs)?;

        let encoding_witness = Num::get_value_multiple(&value_encoding);
        match (
            execute.get_value(),
            encoding_witness,
            value.create_witness(),
            Num::get_value_multiple(&self.tail_state),
        ) {
            (
                Some(execute),
                Some(pushed_value_encoding),
                Some(pushed_value_witness),
                Some(tail_state),
            ) => {
                if execute {
                    self.witness
                        .push(pushed_value_encoding, pushed_value_witness, tail_state);
                }
            }
            _ => {}
        }

        let final_state_candidate =
            fixed_width_hash_into_state_using_optimizer::<_, _, _, AWIDTH, SWIDTH, N>(
                cs,
                &value_encoding,
                &self.tail_state,
                id,
                *execute,
                optimizer,
            )?;

        let new_tail_state = <[Num<E>; SWIDTH]>::conditionally_select(
            cs,
            execute,
            &final_state_candidate,
            &self.tail_state,
        )?;

        self.tail_state = new_tail_state;

        Ok(())
    }

    // outputs round functions inputs and outputs to enforce relation later
    #[track_caller]
    pub fn push_and_output_states_relation<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        value: &I,
        execute: &Boolean,
        round_function: &R,
    ) -> Result<Vec<([Num<E>; SWIDTH], [Num<E>; SWIDTH])>, SynthesisError> {
        assert!(N % AWIDTH == 0);

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;
        let value_encoding = value.encode(cs)?;

        let encoding_witness = Num::get_value_multiple(&value_encoding);

        let num_rounds = N / AWIDTH;
        let mut result = Vec::with_capacity(num_rounds);

        // proceed with witness anyway
        match (
            execute.get_value(),
            encoding_witness,
            value.create_witness(),
            Num::get_value_multiple(&self.tail_state),
        ) {
            (
                Some(execute),
                Some(pushed_value_encoding),
                Some(pushed_value_witness),
                Some(tail_state),
            ) => {
                if execute {
                    self.witness
                        .push(pushed_value_encoding, pushed_value_witness, tail_state);
                }
            }
            _ => {}
        };

        // now perform multiround absorbing by providing witness for round function output, but perform absorbtion
        // in the enforcable manner
        let mut current_tail_state = self.tail_state;
        let mut chunks = value_encoding.chunks_exact(AWIDTH);
        for _ in 0..num_rounds {
            let chunk = chunks.next().unwrap();
            let mut provably_absorbed = current_tail_state;
            for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(chunk.iter()) {
                *dst = dst.add(cs, src)?;
            }

            let round_function_output_witness = match Num::get_value_multiple(&provably_absorbed) {
                Some(provably_absorbed) => {
                    if execute.get_value().unwrap_or(false) {
                        Some(round_function.simulate_round_function(provably_absorbed))
                    } else {
                        Some([E::Fr::zero(); SWIDTH])
                    }
                }
                _ => None,
            };

            let intermediate_candidate = Num::alloc_multiple(cs, round_function_output_witness)?;

            result.push((current_tail_state, intermediate_candidate));
            current_tail_state = intermediate_candidate;
        }

        assert!(chunks.remainder().is_empty());

        let last_state = result.last().unwrap().1;
        self.tail_state = last_state;

        Ok(result)
    }

    // outputs round functions inputs and outputs to enforce relation later
    #[track_caller]
    pub fn push_and_output_states_relation_raw<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        cs: &mut CS,
        value: &I,
        execute: &Boolean,
        current_tail_state: [Num<E>; SWIDTH],
        current_num_items: UInt32<E>,
        round_function: &R,
    ) -> Result<(Vec<([Num<E>; SWIDTH], [Num<E>; SWIDTH])>, UInt32<E>), SynthesisError> {
        assert!(N % AWIDTH == 0);

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = current_num_items.speculative_add(cs, &one_uint32, &execute)?;
        let value_encoding = value.encode(cs)?;

        let num_rounds = N / AWIDTH;
        let mut result = Vec::with_capacity(num_rounds);

        // now perform multiround absorbing by providing witness for round function output, but perform absorbtion
        // in the enforcable manner
        let mut current_tail_state = current_tail_state;
        let mut chunks = value_encoding.chunks_exact(AWIDTH);
        for _ in 0..num_rounds {
            let chunk = chunks.next().unwrap();
            let mut provably_absorbed = current_tail_state;
            for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(chunk.iter()) {
                *dst = dst.add(cs, src)?;
            }

            let round_function_output_witness = match Num::get_value_multiple(&provably_absorbed) {
                Some(provably_absorbed) => {
                    // println!("Initial sponge = {:?}", provably_absorbed);
                    if execute.get_value().unwrap_or(false) {
                        let simulated_state =
                            round_function.simulate_round_function(provably_absorbed);

                        // println!("Final sponge = {:?}", simulated_state);
                        Some(simulated_state)
                    } else {
                        // println!("Sponge is not used");

                        Some([E::Fr::zero(); SWIDTH])
                    }
                }
                _ => None,
            };

            let intermediate_candidate = Num::alloc_multiple(cs, round_function_output_witness)?;

            result.push((provably_absorbed, intermediate_candidate));
            current_tail_state = intermediate_candidate;
        }

        assert!(chunks.remainder().is_empty());

        Ok((result, num_items))
    }

    #[track_caller]
    pub fn push<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        value: &I,
        execute: &Boolean,
        round_function: &R,
    ) -> Result<(), SynthesisError> {
        assert!(N % AWIDTH == 0);

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;
        let value_encoding = value.encode(cs)?;

        let encoding_witness = Num::get_value_multiple(&value_encoding);
        match (
            execute.get_value(),
            encoding_witness,
            value.create_witness(),
            Num::get_value_multiple(&self.tail_state),
        ) {
            (
                Some(execute),
                Some(pushed_value_encoding),
                Some(pushed_value_witness),
                Some(tail_state),
            ) => {
                if execute {
                    self.witness
                        .push(pushed_value_encoding, pushed_value_witness, tail_state);
                }
            }
            _ => {}
        }

        let final_state_candidate = fixed_width_absorb_into_state::<_, _, _, AWIDTH, SWIDTH, N>(
            cs,
            &value_encoding,
            &self.tail_state,
            round_function,
        )?;

        let new_tail_state = <[Num<E>; SWIDTH]>::conditionally_select(
            cs,
            execute,
            &final_state_candidate,
            &self.tail_state,
        )?;

        self.tail_state = new_tail_state;

        Ok(())
    }

    #[track_caller]
    pub fn push_raw<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        encoding: &[Num<E>; N],
        execute: &Boolean,
        round_function: &R,
    ) -> Result<(), SynthesisError> {
        assert!(N % AWIDTH == 0);

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;

        let final_state_candidate = fixed_width_absorb_into_state::<_, _, _, AWIDTH, SWIDTH, N>(
            cs,
            &encoding,
            &self.tail_state,
            round_function,
        )?;

        let new_tail_state = <[Num<E>; SWIDTH]>::conditionally_select(
            cs,
            execute,
            &final_state_candidate,
            &self.tail_state,
        )?;

        self.tail_state = new_tail_state;

        Ok(())
    }

    #[track_caller]
    pub fn push_raw2<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        new_tail_candidate: &[Num<E>; SWIDTH],
        execute: &Boolean,
    ) -> Result<(), SynthesisError> {
        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;

        let new_tail_state = <[Num<E>; SWIDTH]>::conditionally_select(
            cs,
            execute,
            &new_tail_candidate,
            &self.tail_state,
        )?;
        self.tail_state = new_tail_state;

        Ok(())
    }

    #[track_caller]
    pub fn push_raw3<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        new_tail_candidate: [Num<E>; SWIDTH],
        elems_added: UInt32<E>,
    ) -> Result<(), SynthesisError> {
        let num_items = self.num_items.add_unchecked(cs, &elems_added)?;
        self.num_items = num_items;
        self.tail_state = new_tail_candidate;

        Ok(())
    }

    #[track_caller]
    pub fn pop_first_with_optimizer<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        id: u64,
        execute: &Boolean,
        optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
    ) -> Result<I, SynthesisError> {
        // note that when we do pop we can not know if we pop a proper item
        // and instead we just continue to drain until we hit the empty state, when we
        // have to compare that head state == tail state and number of items == 0

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_sub(cs, &one_uint32, &execute)?;
        self.num_items = num_items;

        let (encoding_witness, value_witness) = if let Some(execute_witness) = execute.get_value() {
            if execute_witness {
                let value = self.witness.pop_first();

                (Some(value.0), Some(value.1))
            } else {
                // Some irrelevant witness
                let enc_wit = [E::Fr::zero(); N];

                (Some(enc_wit), Some(I::placeholder_witness()))
            }
        } else {
            (None, None)
        };

        let encoding = Num::alloc_multiple(cs, encoding_witness)?;

        let popped =
            self.pop_first_inner_with_optimizer::<_, _>(cs, id, execute, encoding, optimizer)?;

        let item =
            I::allocate_and_prove_encoding_conditionally(cs, &popped, &execute, value_witness)?;

        Ok(item)
    }

    #[track_caller]
    pub fn pop_first<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        execute: &Boolean,
        round_function: &R,
    ) -> Result<I, SynthesisError> {
        let (item, _) = self.pop_first_and_return_encoding(cs, execute, round_function)?;

        Ok(item)
    }

    #[track_caller]
    pub fn pop_first_and_return_encoding<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        execute: &Boolean,
        round_function: &R,
    ) -> Result<(I, [Num<E>; N]), SynthesisError> {
        // note that when we do pop we can not know if we pop a proper item
        // and instead we just continue to drain until we hit the empty state, when we
        // have to compare that head state == tail state and number of items == 0

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_sub(cs, &one_uint32, &execute)?;
        self.num_items = num_items;

        let (encoding_witness, value_witness) = if let Some(execute_witness) = execute.get_value() {
            if execute_witness {
                let value = self.witness.pop_first();

                (Some(value.0), Some(value.1))
            } else {
                // Some irrelevant witness
                let enc_wit = [E::Fr::zero(); N];

                (Some(enc_wit), Some(I::placeholder_witness()))
            }
        } else {
            (None, None)
        };

        let encoding = Num::alloc_multiple(cs, encoding_witness)?;

        let popped = self.pop_first_inner::<_, _>(cs, execute, encoding, round_function)?;

        let item =
            I::allocate_and_prove_encoding_conditionally(cs, &popped, &execute, value_witness)?;

        Ok((item, popped))
    }

    #[track_caller]
    pub fn pop_first_encoding_only<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        execute: &Boolean,
        round_function: &R,
    ) -> Result<[Num<E>; N], SynthesisError> {
        // note that when we do pop we can not know if we pop a proper item
        // and instead we just continue to drain until we hit the empty state, when we
        // have to compare that head state == tail state and number of items == 0

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_sub(cs, &one_uint32, &execute)?;
        self.num_items = num_items;

        let encoding_witness = if let Some(execute_witness) = execute.get_value() {
            if execute_witness {
                let value = self.witness.pop_first();

                Some(value.0)
            } else {
                // Some irrelevant witness
                let enc_wit = [E::Fr::zero(); N];

                Some(enc_wit)
            }
        } else {
            None
        };

        let encoding = Num::alloc_multiple(cs, encoding_witness)?;

        let popped = self.pop_first_inner::<_, _>(cs, execute, encoding, round_function)?;

        Ok(popped)
    }

    #[track_caller]
    fn pop_first_inner_with_optimizer<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        id: u64,
        execute: &Boolean,
        encoding: [Num<E>; N],
        optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
    ) -> Result<[Num<E>; N], SynthesisError> {
        let initial_state = self.head_state;

        let committment = fixed_width_hash_into_state_using_optimizer::<_, _, _, AWIDTH, SWIDTH, N>(
            cs,
            &encoding,
            &initial_state,
            id,
            *execute,
            optimizer,
        )?;

        let new_head_state = committment;

        // update a head
        let new_head = <[Num<E>; SWIDTH]>::conditionally_select(
            cs,
            &execute,
            &new_head_state,
            &self.head_state,
        )?;

        // now check: if we end up in empty state then we must have a head state == tail state
        let is_empty = self.is_empty(cs)?;
        let head_is_equal_to_tail = compare_nums(cs, &new_head, &self.tail_state)?;

        // we only conditionally change the queue length, so we can not have the we execute and that
        // queue became empty and head != tail, so just enforce
        Boolean::enforce_equal(cs, &is_empty, &head_is_equal_to_tail)?;

        self.head_state = new_head;

        Ok(encoding)
    }

    #[track_caller]
    fn pop_first_inner<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
    >(
        &mut self,
        cs: &mut CS,
        execute: &Boolean,
        encoding: [Num<E>; N],
        round_function: &R,
    ) -> Result<[Num<E>; N], SynthesisError> {
        let initial_state = self.head_state;

        let committment = fixed_width_absorb_into_state::<_, _, _, AWIDTH, SWIDTH, N>(
            cs,
            &encoding,
            &initial_state,
            round_function,
        )?;

        let new_head_state = committment;

        // update a head
        let new_head = <[Num<E>; SWIDTH]>::conditionally_select(
            cs,
            &execute,
            &new_head_state,
            &self.head_state,
        )?;

        // now check: if we end up in empty state then we must have a head state == tail state
        let is_empty = self.is_empty(cs)?;

        for (a, b) in new_head.iter().zip(self.tail_state.iter()) {
            Num::conditionally_enforce_equal(cs, &is_empty, a, b)?;
        }

        // let head_is_equal_to_tail = compare_nums(cs, &new_head, &self.tail_state)?;

        // // we only conditionally change the queue length, so we can not have the we execute and that
        // // queue became empty and head != tail, so just enforce
        // Boolean::enforce_equal(cs, &is_empty, &head_is_equal_to_tail)?;

        self.head_state = new_head;

        Ok(encoding)
    }

    pub fn is_empty<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError> {
        self.num_items.is_zero(cs)
    }

    pub fn get_head_state(&self) -> [Num<E>; SWIDTH] {
        self.head_state
    }

    pub fn get_tail_state(&self) -> [Num<E>; SWIDTH] {
        self.tail_state
    }

    pub fn get_final_state_compact_encoding(&self) -> Num<E> {
        self.tail_state[0]
    }

    pub fn len(&self) -> UInt32<E> {
        self.num_items
    }

    pub fn split<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        at: UInt32<E>,
    ) -> Result<(Self, Self), SynthesisError> {
        // we need some hints from witness
        let split_at = at.get_value().map(|el| el as usize);
        let (intermediate_tail_state, _) = self.witness.some_split_hint(split_at);
        // tail is non-trivial is self.length > at
        let (may_be_tail_length, borrow) = self.num_items.sub(cs, &at)?;
        let may_be_tail_length_is_zero = may_be_tail_length.inner.is_zero(cs)?;
        let tail_is_trivial = smart_or(cs, &[may_be_tail_length_is_zero, borrow])?;

        let intermediate_tail_state = Num::alloc_multiple(cs, intermediate_tail_state)?;
        let tail_is_non_trivial = tail_is_trivial.not();

        // if tail is trivial then we just take a full length
        let first_length =
            UInt32::conditionally_select(cs, &tail_is_trivial, &self.num_items, &at)?;

        // if we have seen borrow then tail length is 0, otherwise it will be
        // either 0 or >0, but it's captured in `may_be_tail_length`
        let tail_length =
            UInt32::conditionally_select(cs, &borrow, &UInt32::zero(), &may_be_tail_length)?;

        let first_part_tail = <[Num<E>; SWIDTH]>::conditionally_select(
            cs,
            &tail_is_non_trivial,
            &intermediate_tail_state,
            &self.tail_state,
        )?;

        // try to split a witness
        let (first_witness, second_witness) = self.witness.some_split(split_at);

        let first = Self {
            head_state: self.head_state,
            tail_state: first_part_tail,
            num_items: first_length,
            witness: first_witness,
        };

        let second = Self {
            head_state: first_part_tail,
            tail_state: self.tail_state,
            num_items: tail_length,
            witness: second_witness,
        };

        Ok((first, second))
    }

    pub fn enforce_to_be_empty<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let len_is_zero = self.num_items.is_zero(cs)?;
        let mut tmp = vec![];
        for (h, t) in self.head_state.iter().zip(self.tail_state.iter()) {
            let e = Num::equals(cs, h, t)?;
            tmp.push(e);
        }
        let head_is_equal_to_tail = smart_and(cs, &tmp)?;

        Boolean::enforce_equal(cs, &len_is_zero, &head_is_equal_to_tail)?;
        Boolean::enforce_equal(cs, &len_is_zero, &Boolean::Constant(true))?;

        Ok(())
    }

    pub fn enforce_to_be_not_empty<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let len_is_zero = self.num_items.is_zero(cs)?;
        let mut tmp = vec![];
        for (h, t) in self.head_state.iter().zip(self.tail_state.iter()) {
            let e = Num::equals(cs, h, t)?;
            tmp.push(e);
        }
        let head_is_equal_to_tail = smart_and(cs, &tmp)?;

        Boolean::enforce_equal(cs, &len_is_zero, &head_is_equal_to_tail)?;
        Boolean::enforce_equal(cs, &len_is_zero, &Boolean::Constant(false))?;

        Ok(())
    }
}

use crate::scheduler::queues::FullSpongeLikeQueueState;

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
    > FixedWidthEncodingSpongeLikeQueue<E, I, N, 2, 3>
{
    pub fn from_state<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        state: FullSpongeLikeQueueState<E>,
    ) -> Result<Self, SynthesisError> {
        let FullSpongeLikeQueueState { length, head, tail } = state;

        Self::from_raw_parts(cs, head, tail, length)
    }

    pub fn into_state(self) -> FullSpongeLikeQueueState<E> {
        FullSpongeLikeQueueState {
            length: self.num_items,
            head: self.head_state,
            tail: self.tail_state,
        }
    }
}

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
        const AWIDTH: usize,
        const SWIDTH: usize,
    > CircuitEq<E> for FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>
{
    fn eq(&self, other: &Self) -> bool {
        self.num_items.eq(&other.num_items)
            && self.head_state.eq(&other.head_state)
            && self.tail_state.eq(&other.tail_state)
    }
}

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
        const AWIDTH: usize,
        const SWIDTH: usize,
    > CircuitSelectable<E> for FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>
{
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        if a.eq(b) {
            return Ok(a.clone());
        }

        let witness = if let Some(flag) = flag.get_value() {
            if flag {
                a.witness.clone()
            } else {
                b.witness.clone()
            }
        } else {
            FixedWidthEncodingSpongeLikeQueueWitness::empty()
        };

        let num_items = UInt32::conditionally_select(cs, flag, &a.num_items, &b.num_items)?;
        let head_state =
            <[Num<E>; SWIDTH]>::conditionally_select(cs, flag, &a.head_state, &b.head_state)?;
        let tail_state =
            <[Num<E>; SWIDTH]>::conditionally_select(cs, flag, &a.tail_state, &b.tail_state)?;

        let new = Self {
            num_items,
            head_state,
            tail_state,
            witness,
        };

        Ok(new)
    }
}
