use super::saved_contract_context::*;
use super::*;
use crate::traits::*;
use crate::vm::primitives::u160;
use cs_derive::*;

// execution context that keeps all explicit data about the current execution frame,
// and avoid recomputing of quantities that also do not change between calls
#[derive(
    Derivative, CSAllocatable, CSWitnessable, CSEqual, CSSelectable, CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct FullExecutionContext<E: Engine> {
    pub saved_context: ExecutionContextRecord<E>,
    pub log_queue_forward_tail: Num<E>,
    pub log_queue_forward_part_length: UInt32<E>,
}

impl<E: Engine> FullExecutionContext<E> {
    pub fn uninitialized() -> Self {
        Self {
            saved_context: ExecutionContextRecord::uninitialized(),
            log_queue_forward_tail: Num::<E>::zero(),
            log_queue_forward_part_length: UInt32::<E>::zero(),
        }
    }
}

impl<E: Engine> Copy for FullExecutionContext<E> {}
