use super::*;

pub mod aux_tables;
pub mod keccak256;
pub mod sha256;
pub mod utils;

use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::SynthesisError;
use crate::circuit_structures::utils::*;
use crate::ff::{Field, PrimeField, ScalarEngine};
use crate::franklin_crypto::plonk::circuit::allocated_num::*;
use crate::franklin_crypto::plonk::circuit::boolean::*;
use crate::franklin_crypto::plonk::circuit::linear_combination::*;
use crate::pairing::Engine;
use crate::vm::partitioner::*;

// universal precompiles passthrough input/output
// takes requests queue + memory state
// outputs memory state

use super::*;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;
use crate::scheduler::queues::FullSpongeLikeQueueState;
use crate::traits::*;
use crate::vm::structural_eq::*;
use cs_derive::*;

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct PrecompileFunctionInputData<E: Engine> {
    pub initial_log_queue_state: FixedWidthEncodingGenericQueueState<E>,
    pub initial_memory_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for PrecompileFunctionInputData<E> {
    fn empty() -> Self {
        Self {
            initial_log_queue_state: FixedWidthEncodingGenericQueueState::<E>::empty(),
            initial_memory_state: FullSpongeLikeQueueState::<E>::empty(),
        }
    }
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct PrecompileFunctionOutputData<E: Engine> {
    pub final_memory_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for PrecompileFunctionOutputData<E> {
    fn empty() -> Self {
        Self {
            final_memory_state: FullSpongeLikeQueueState::<E>::empty(),
        }
    }
}
