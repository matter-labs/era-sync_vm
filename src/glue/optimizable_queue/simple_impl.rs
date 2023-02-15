use super::super::traits::*;
use super::utils::*;
use super::*;
use crate::bellman::SynthesisError;
use crate::circuit_structures::traits::*;
use crate::derivative::*;
use crate::ff::*;
use crate::vm::optimizer::sponge_set::*;
use crate::ConstraintSystem;
use crate::{pairing::*, vm::primitives::UInt32};
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::Assignment;
use franklin_crypto::rescue::*;
use smallvec::SmallVec;
use std::collections::VecDeque;
use std::convert::TryInto;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
pub struct FixedWidthEncodingGenericQueueWitness<
    E: Engine,
    I: CircuitFixedLengthEncodableExt<E, N>,
    const N: usize,
> {
    #[serde(bound(
        serialize = "[E::Fr; N]: serde::Serialize, <I as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "[E::Fr; N]: serde::de::DeserializeOwned, <I as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub wit: VecDeque<([E::Fr; N], <I as CSWitnessable<E>>::Witness, E::Fr)>,
}

impl<E: Engine, I: CircuitFixedLengthEncodableExt<E, N>, const N: usize> Default
    for FixedWidthEncodingGenericQueueWitness<E, I, N>
{
    fn default() -> Self {
        Self::empty()
    }
}

impl<E: Engine, I: CircuitFixedLengthEncodableExt<E, N>, const N: usize> CircuitEmpty<E>
    for FixedWidthEncodingGenericQueueWitness<E, I, N>
{
    fn empty() -> Self {
        Self {
            wit: VecDeque::new(),
        }
    }
}

impl<E: Engine, I: CircuitFixedLengthEncodableExt<E, N>, const N: usize>
    FixedWidthEncodingGenericQueueWitness<E, I, N>
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
        previous_tail: E::Fr,
    ) {
        self.wit
            .push_back((new_item_encoding, new_item_witness, previous_tail));
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.wit.is_empty()
    }

    pub(crate) fn some_split_hint(&self, at: Option<usize>) -> (Option<E::Fr>, Option<bool>) {
        if let Some(at) = at {
            let (intermediate, non_trivial) = self.split_hint(at);
            (Some(intermediate), Some(non_trivial))
        } else {
            (None, None)
        }
    }

    pub(crate) fn split_hint(&self, at: usize) -> (E::Fr, bool) {
        if self.wit.len() <= at {
            return (E::Fr::zero(), false);
        } else {
            let (_, _, tail) = &self.wit[at];
            return (*tail, true);
        }
    }

    pub(crate) fn split(mut self, at: usize) -> (Self, Self) {
        if at >= self.wit.len() {
            return (self, Self::empty());
        }

        let first_wit: VecDeque<_> = self.wit.drain(..(at as usize)).collect();
        let rest_wit = self.wit;

        let first = Self { wit: first_wit };

        let rest = Self { wit: rest_wit };

        (first, rest)
    }

    pub(crate) fn some_split(self, at: Option<usize>) -> (Self, Self) {
        if let Some(at) = at {
            self.split(at)
        } else {
            (Self::empty(), Self::empty())
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct FixedWidthEncodingGenericQueue<
    E: Engine,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
> {
    pub(crate) num_items: UInt32<E>,
    pub(crate) head_state: Num<E>,
    pub(crate) tail_state: Num<E>,
    #[derivative(Debug = "ignore")]
    pub(crate) witness: FixedWidthEncodingGenericQueueWitness<E, I, N>,
}

use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
    > FixedWidthEncodingGenericQueue<E, I, N>
{
    pub fn empty() -> Self {
        let empty_num = Num::zero();
        Self {
            num_items: UInt32::zero(),
            head_state: empty_num,
            tail_state: empty_num,
            witness: FixedWidthEncodingGenericQueueWitness::<E, I, N>::empty(),
        }
    }

    pub fn from_state<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        state: FixedWidthEncodingGenericQueueState<E>,
    ) -> Result<Self, SynthesisError> {
        let FixedWidthEncodingGenericQueueState {
            num_items,
            head_state,
            tail_state,
        } = state;

        Self::from_raw_parts(cs, head_state, tail_state, num_items)
    }

    pub fn into_state(self) -> FixedWidthEncodingGenericQueueState<E> {
        FixedWidthEncodingGenericQueueState {
            num_items: self.num_items,
            head_state: self.head_state,
            tail_state: self.tail_state,
        }
    }

    pub fn from_raw_parts<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        head: Num<E>,
        tail: Num<E>,
        length: UInt32<E>,
    ) -> Result<Self, SynthesisError> {
        let length_is_zero = length.is_zero(cs)?;
        let head_is_equal_to_tail = Num::equals(cs, &head, &tail)?;
        Boolean::enforce_equal(cs, &length_is_zero, &head_is_equal_to_tail)?;

        let new = Self {
            num_items: length,
            head_state: head,
            tail_state: tail,
            witness: FixedWidthEncodingGenericQueueWitness::<E, I, N>::empty(),
        };

        Ok(new)
    }

    pub fn from_tail_and_length<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        tail: Num<E>,
        length: UInt32<E>,
    ) -> Result<Self, SynthesisError> {
        let length_is_zero = length.is_zero(cs)?;
        let tail_is_zero = tail.is_zero(cs)?;
        Boolean::enforce_equal(cs, &length_is_zero, &tail_is_zero)?;

        let new = Self {
            num_items: length,
            head_state: Num::zero(),
            tail_state: tail,
            witness: FixedWidthEncodingGenericQueueWitness::<E, I, N>::empty(),
        };

        Ok(new)
    }

    #[track_caller]
    pub fn push_with_optimizer<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        id: u64,
        value: &I,
        execute: &Boolean,
        optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
    ) -> Result<(), SynthesisError> {
        // we take a state and make new tail state = hash(tail state, value_encoding)
        // later on to pop the witness from the beginning we will need an old tail state
        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;
        let value_encoding = value.encode(cs)?;

        let encoding_witness = Num::get_value_multiple(&value_encoding);
        match (
            execute.get_value(),
            encoding_witness,
            value.create_witness(),
            self.tail_state.get_value(),
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

        let mut input = SmallVec::<[_; 9]>::new();
        input.extend_from_slice(&value_encoding);
        input.push(self.tail_state.clone());

        let committment = variable_length_hash_using_optimizer::<_, _, _, AWIDTH, SWIDTH>(
            cs, &input, id, *execute, optimizer,
        )?;

        let new_tail_state =
            Num::conditionally_select(cs, execute, &committment, &self.tail_state)?;

        self.tail_state = new_tail_state;

        Ok(())
    }

    #[track_caller]
    pub(crate) fn push_raw<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        value_encoding: [Num<E>; N],
        witness: Option<I::Witness>,
        execute: &Boolean,
        round_function: &R,
    ) -> Result<(), SynthesisError> {
        // almost like a push function, but for a case when we want to do a lot of selects outside and push only once
        // versus "_with_optimizer" function that shares a sponge rounds with other non-queue like actions

        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;
        let pushed_value_encoding = Num::get_value_multiple(&value_encoding);
        match (
            execute.get_value(),
            witness,
            pushed_value_encoding,
            self.tail_state.get_value(),
        ) {
            (
                Some(execute),
                Some(pushed_value_witness),
                Some(pushed_value_encoding),
                Some(tail_state),
            ) => {
                if execute {
                    self.witness
                        .push(pushed_value_encoding, pushed_value_witness, tail_state);
                }
            }
            _ => {}
        }

        let mut input = SmallVec::<[_; 9]>::new();
        input.extend_from_slice(&value_encoding);
        input.push(self.tail_state.clone());

        let committment =
            variable_length_hash::<_, _, _, AWIDTH, SWIDTH>(cs, &input, round_function)?;

        let new_tail_state =
            Num::conditionally_select(cs, execute, &committment, &self.tail_state)?;

        self.tail_state = new_tail_state;

        Ok(())
    }

    #[track_caller]
    pub(crate) fn push_raw_with_optimizer<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        id: u64,
        value_encoding: [Num<E>; N],
        witness: Option<I::Witness>,
        execute: &Boolean,
        optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
    ) -> Result<(), SynthesisError> {
        // almost like a push function, but for a case when we want to do a lot of selects outside and push only once
        // versus "_with_optimizer" function that shares a sponge rounds with other non-queue like actions

        let num_items = self
            .num_items
            .speculative_add(cs, &UInt32::from_uint(1u32), &execute)?;
        self.num_items = num_items;
        let pushed_value_encoding = Num::get_value_multiple(&value_encoding);
        match (
            execute.get_value(),
            witness,
            pushed_value_encoding,
            self.tail_state.get_value(),
        ) {
            (
                Some(execute),
                Some(pushed_value_witness),
                Some(pushed_value_encoding),
                Some(tail_state),
            ) => {
                if execute {
                    self.witness
                        .push(pushed_value_encoding, pushed_value_witness, tail_state);
                }
            }
            _ => {}
        }

        let mut input = SmallVec::<[_; 9]>::new();
        input.extend_from_slice(&value_encoding);
        input.push(self.tail_state.clone());

        let committment = variable_length_hash_using_optimizer::<_, _, _, AWIDTH, SWIDTH>(
            cs, &input, id, *execute, optimizer,
        )?;

        let new_tail_state =
            Num::conditionally_select(cs, execute, &committment, &self.tail_state)?;

        self.tail_state = new_tail_state;

        Ok(())
    }

    #[track_caller]
    pub fn push<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        value: &I,
        execute: &Boolean,
        round_function: &R,
    ) -> Result<(), SynthesisError> {
        // we take a state and make new tail state = hash(tail state, value_encoding)
        // later on to pop the witness from the beginning we will need an old tail state
        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = self.num_items.speculative_add(cs, &one_uint32, &execute)?;
        self.num_items = num_items;
        let value_encoding = value.encode(cs)?;

        let encoding_witness = Num::get_value_multiple(&value_encoding);
        match (
            execute.get_value(),
            encoding_witness,
            value.create_witness(),
            self.tail_state.get_value(),
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

        let mut input = SmallVec::<[_; 9]>::new();
        input.extend_from_slice(&value_encoding);
        input.push(self.tail_state.clone());

        let committment =
            variable_length_hash::<_, _, _, AWIDTH, SWIDTH>(cs, &input, round_function)?;

        let new_tail_state =
            Num::conditionally_select(cs, execute, &committment, &self.tail_state)?;

        self.tail_state = new_tail_state;

        Ok(())
    }

    #[track_caller]
    pub fn pop_first_with_optimizer<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
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

        let popped = self.pop_first_inner_with_optimizer::<_, _, AWIDTH, SWIDTH>(
            cs, id, execute, encoding, optimizer,
        )?;

        let item =
            I::allocate_and_prove_encoding_conditionally(cs, &popped, &execute, value_witness)?;

        Ok(item)
    }

    fn pop_first_inner_with_optimizer<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        id: u64,
        execute: &Boolean,
        encoding: [Num<E>; N],
        optimizer: &mut SpongeOptimizer<E, R, AWIDTH, SWIDTH>,
    ) -> Result<[Num<E>; N], SynthesisError> {
        let mut input = vec![];
        input.extend_from_slice(&encoding);
        input.push(self.head_state.clone());

        let committment = variable_length_hash_using_optimizer::<_, _, _, AWIDTH, SWIDTH>(
            cs, &input, id, *execute, optimizer,
        )?;
        let new_head_state = committment;

        // update a head
        let new_head = Num::conditionally_select(cs, &execute, &new_head_state, &self.head_state)?;

        // now check: if we end up in empty state then we must have a head state == tail state
        let is_empty = self.is_empty(cs)?;
        let head_is_equal_to_tail = Num::equals(cs, &new_head, &self.tail_state)?;

        // we only conditionally change the queue length, so we can not have the we execute and that
        // queue became empty and head != tail, so just enforce
        Boolean::enforce_equal(cs, &is_empty, &head_is_equal_to_tail)?;

        self.head_state = new_head;

        Ok(encoding)
    }

    #[track_caller]
    pub fn pop_first<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        execute: &Boolean,
        round_function: &R,
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
            self.pop_first_inner::<_, _, AWIDTH, SWIDTH>(cs, execute, encoding, round_function)?;

        let item =
            I::allocate_and_prove_encoding_conditionally(cs, &popped, &execute, value_witness)?;

        Ok(item)
    }

    #[track_caller]
    pub fn pop_first_and_return_encoding<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
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

        let popped =
            self.pop_first_inner::<_, _, AWIDTH, SWIDTH>(cs, execute, encoding, round_function)?;

        let item =
            I::allocate_and_prove_encoding_conditionally(cs, &popped, &execute, value_witness)?;

        Ok((item, popped))
    }

    #[track_caller]
    pub fn pop_first_encoding_only<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
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

        let popped =
            self.pop_first_inner::<_, _, AWIDTH, SWIDTH>(cs, execute, encoding, round_function)?;

        Ok(popped)
    }

    #[track_caller]
    fn pop_first_inner<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        execute: &Boolean,
        encoding: [Num<E>; N],
        round_function: &R,
    ) -> Result<[Num<E>; N], SynthesisError> {
        let mut input = vec![];
        input.extend_from_slice(&encoding);
        input.push(self.head_state.clone());

        let committment =
            variable_length_hash::<_, _, _, AWIDTH, SWIDTH>(cs, &input, round_function)?;
        let new_head_state = committment;

        // update a head
        let new_head = Num::conditionally_select(cs, &execute, &new_head_state, &self.head_state)?;

        // now check: if we end up in empty state then we must have a head state == tail state
        let is_empty = self.is_empty(cs)?;
        Num::conditionally_enforce_equal(cs, &is_empty, &new_head, &self.tail_state)?;

        self.head_state = new_head;

        Ok(encoding)
    }

    pub fn is_empty<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError> {
        self.num_items.is_zero(cs)
    }

    pub fn get_head_state(&self) -> Num<E> {
        self.head_state.clone()
    }

    pub fn get_tail_state(&self) -> Num<E> {
        self.tail_state.clone()
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

        let intermediate_tail_state = Num::alloc(cs, intermediate_tail_state)?;
        let tail_is_non_trivial = tail_is_trivial.not();

        // if tail is trivial then we just take a full length
        let first_length =
            UInt32::conditionally_select(cs, &tail_is_trivial, &self.num_items, &at)?;

        // if we have seen borrow then tail length is 0, otherwise it will be
        // either 0 or >0, but it's captured in `may_be_tail_length`
        let tail_length =
            UInt32::conditionally_select(cs, &borrow, &UInt32::zero(), &may_be_tail_length)?;

        let first_part_tail = Num::conditionally_select(
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
        let head_is_equal_to_tail = Num::equals(cs, &self.head_state, &self.tail_state)?;

        Boolean::enforce_equal(cs, &len_is_zero, &head_is_equal_to_tail)?;
        Boolean::enforce_equal(cs, &len_is_zero, &Boolean::Constant(true))?;

        Ok(())
    }

    pub fn enforce_to_be_not_empty<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let len_is_zero = self.num_items.is_zero(cs)?;
        let head_is_equal_to_tail = Num::equals(cs, &self.head_state, &self.tail_state)?;

        Boolean::enforce_equal(cs, &len_is_zero, &head_is_equal_to_tail)?;
        Boolean::enforce_equal(cs, &len_is_zero, &Boolean::Constant(false))?;

        Ok(())
    }

    // outputs round functions inputs and outputs to enforce relation later
    #[track_caller]
    pub fn push_and_output_states_relation_raw<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        cs: &mut CS,
        value: &I,
        execute: &Boolean,
        current_tail_state: Num<E>,
        current_num_items: UInt32<E>,
        round_function: &R,
    ) -> Result<(Vec<([Num<E>; SWIDTH], [Num<E>; SWIDTH])>, Num<E>, UInt32<E>), SynthesisError>
    {
        let one_uint32 = UInt32::constant(E::Fr::one());
        let num_items = current_num_items.speculative_add(cs, &one_uint32, &execute)?;
        let value_encoding = value.encode(cs)?;

        let mut encoding: Vec<_> = value_encoding.to_vec();
        encoding.push(current_tail_state);

        assert!(encoding.len() % AWIDTH == 0);

        let num_rounds = encoding.len() / AWIDTH;
        let mut result = Vec::with_capacity(num_rounds);

        // now perform multiround absorbing by providing witness for round function output, but perform absorbtion
        // in the enforcable manner
        let mut current_state = R::empty_state();
        current_state = round_function.apply_length_specialization(current_state, encoding.len());

        let mut chunks = encoding.chunks_exact(AWIDTH);
        for round_idx in 0..num_rounds {
            let chunk = chunks.next().unwrap();
            let mut provably_absorbed = current_state;

            if round_idx == 0 {
                // just set
                for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(chunk.iter()) {
                    *dst = *src;
                }
            } else {
                // absorb by addition
                for (dst, src) in provably_absorbed[..AWIDTH].iter_mut().zip(chunk.iter()) {
                    *dst = dst.add(cs, src)?;
                }
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
            current_state = intermediate_candidate;
            result.push((provably_absorbed, intermediate_candidate));
        }

        let output = R::state_into_commitment(result.last().unwrap().1)?;

        assert!(chunks.remainder().is_empty());

        Ok((result, output, num_items))
    }
}

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
    > CircuitEq<E> for FixedWidthEncodingGenericQueue<E, I, N>
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
    > CircuitSelectable<E> for FixedWidthEncodingGenericQueue<E, I, N>
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
            FixedWidthEncodingGenericQueueWitness::empty()
        };

        let num_items = UInt32::conditionally_select(cs, flag, &a.num_items, &b.num_items)?;
        let head_state = Num::conditionally_select(cs, flag, &a.head_state, &b.head_state)?;
        let tail_state = Num::conditionally_select(cs, flag, &a.tail_state, &b.tail_state)?;

        let new = Self {
            num_items,
            head_state,
            tail_state,
            witness,
        };

        Ok(new)
    }
}
