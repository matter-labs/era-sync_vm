use std::collections::VecDeque;

use franklin_crypto::{
    bellman::{Engine, Field, PrimeField},
    plonk::circuit::allocated_num::Num,
};

use crate::glue::CSWitnessable;
use crate::{
    circuit_structures::traits::CircuitArithmeticRoundFunction,
    traits::{FixedLengthDecodable, FixedLengthEncodable},
};

pub struct FixedWidthWitnessQueue<
    E: Engine,
    I: FixedLengthEncodable<E, N> + FixedLengthDecodable<E, N>,
    const N: usize,
> {
    head_state: E::Fr,
    tail_state: E::Fr,
    num_items: u32,
    inner_map: VecDeque<([E::Fr; N], I)>,
}

impl<E: Engine, I: FixedLengthEncodable<E, N> + FixedLengthDecodable<E, N>, const N: usize>
    FixedWidthWitnessQueue<E, I, N>
{
    pub fn empty() -> Self {
        Self {
            head_state: E::Fr::zero(),
            tail_state: E::Fr::zero(),
            num_items: 0,
            inner_map: VecDeque::new(),
        }
    }

    pub fn push<
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        value: &I,
        execute: bool,
        round_function: &R,
    ) {
        if execute == false {
            return;
        }
        let tail_state = self.tail_state.clone();
        let encoding = value.encode();
        let mut full_encoding = vec![tail_state];
        full_encoding.extend_from_slice(&encoding);
        self.tail_state = Self::variable_length_hash(&full_encoding, round_function);
        self.inner_map.push_back((encoding, value.clone()));
    }

    pub fn pop<
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        execute: bool,
        round_function: &R,
    ) -> I {
        if execute == false || self.inner_map.len() < 1 {
            return I::placeholder();
        }

        let (encoding, item) = self.inner_map.pop_front().expect("item");
        let mut full_encoding = vec![self.head_state];
        full_encoding.extend_from_slice(&encoding);
        self.head_state = Self::variable_length_hash(&full_encoding, round_function);

        item
    }

    fn variable_length_hash<
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        _input: &[E::Fr],
        _round_function: &R,
    ) -> E::Fr {
        unimplemented!();
    }

    pub fn get_tail_state(&self) -> E::Fr {
        self.tail_state
    }
    pub fn get_head_state(&self) -> E::Fr {
        self.head_state
    }
    pub fn is_empty(&self) -> bool {
        self.inner_map.is_empty()
    }
    pub fn len(&self) -> u32 {
        self.inner_map.len() as u32
    }
}
