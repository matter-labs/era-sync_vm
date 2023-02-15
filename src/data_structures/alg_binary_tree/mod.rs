pub mod dense_tree;
pub mod rescue_impl;
pub mod sparse_tree;

use crate::ff::*;
use std::fmt::Debug;

pub use self::dense_tree::*;

pub trait AlgebraicBinaryTreeInnerHasher<F: PrimeField>: Sized + Send + Sync + Clone {
    type InOut: Sized + Clone + Copy + Send + Sync + PartialEq + Eq + Debug;

    fn placeholder_output() -> Self::InOut;
    fn node_hash(&self, input: &[Self::InOut; 2], level: usize) -> Self::InOut;
}
