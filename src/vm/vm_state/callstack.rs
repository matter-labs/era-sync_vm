use super::execution_context::*;
use super::*;
use crate::traits::*;

#[derive(
    Derivative, CSAllocatable, CSWitnessable, CSEqual, CSSelectable, CSVariableLengthEncodable,
)]
#[derivative(Clone, Copy, Debug)]
pub struct Callstack<E: Engine, const SWIDTH: usize> {
    pub current_context: FullExecutionContext<E>,
    pub context_stack_depth: UInt32<E>,
    pub stack_sponge_state: [Num<E>; SWIDTH],
}

impl<E: Engine, const SWIDTH: usize> Callstack<E, SWIDTH> {
    pub fn empty() -> Self {
        Self {
            current_context: FullExecutionContext::uninitialized(),
            context_stack_depth: UInt32::zero(),
            stack_sponge_state: [Num::<E>::zero(); SWIDTH],
        }
    }

    pub fn is_empty<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError> {
        self.context_stack_depth.is_zero(cs)
    }

    pub fn is_full<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        UInt32::equals(
            cs,
            &self.context_stack_depth,
            &UInt32::from_uint(zkevm_opcode_defs::system_params::VM_MAX_STACK_DEPTH),
        )
    }
}
