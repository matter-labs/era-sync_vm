use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;

use crate::traits::*;

mod toy_impl;

pub use self::toy_impl::*;

pub trait MerkleTreeBasedStorage<E: Engine>: Clone + Send + Sync {
    type Value: ArithmeticCommitable<E>;
    type Proof: Clone;

    fn get(&self, index: usize) -> Result<(Self::Value, Self::Proof), SynthesisError>;
    fn set(&mut self, index: usize, new_value: Self::Value) -> Result<(), SynthesisError>;
}
