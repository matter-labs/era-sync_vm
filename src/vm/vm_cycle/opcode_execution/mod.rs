use super::*;

use zkevm_opcode_defs::SET_FLAGS_FLAG_IDX;

pub mod add;
pub mod binop;
pub mod context;
pub mod div;
pub mod jump;
pub mod log;
pub mod mul;
pub mod nop;
pub mod ptr;
pub mod shift;
pub mod special_call_ret;
pub mod sub;
pub mod uma;

use crate::vm::vm_cycle::pre_state::*;
use crate::vm::vm_cycle::witness_oracle::WitnessOracle;
use crate::vm::vm_state::GlobalContext;
use crate::vm::vm_state::VmLocalState;

impl<E: Engine> InCircuitOpcode<E> for PropsMarker {
    fn apply<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    >(
        &self, // should be just zkevm_opcode_def structure, or some specialized marker
        cs: &mut CS,
        current_state: &VmLocalState<E, 3>,
        common_opcode_state: &CommonOpcodeState<E>,
        opcode_carry_parts: &OpcodeCarryParts<E>,
        global_context: &GlobalContext<E>,
        optimizer: &mut OptimizationContext<E>,
        round_function: &R,
        witness_oracle: &mut impl WitnessOracle<E>,
    ) -> Result<OpcodePartialApplicationResult<E, Self>, SynthesisError> {
        match self {
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Invalid(_)) => unreachable!(),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Nop(_)) => self::nop::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Add(_)) => self::add::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Sub(_)) => self::sub::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Mul(_)) => self::mul::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Div(_)) => self::div::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Jump(_)) => self::jump::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Context(_)) => self::context::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Shift(_)) => self::shift::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Ptr(_)) => self::ptr::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Binop(_)) => self::binop::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::Log(_)) => self::log::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Normal(zkevm_opcode_defs::Opcode::UMA(_)) => self::uma::apply(
                cs,
                current_state,
                common_opcode_state,
                opcode_carry_parts,
                global_context,
                optimizer,
                round_function,
                witness_oracle,
            ),
            PropsMarker::Specialized(specialization) => {
                let spec_result = match specialization {
                    SpecializedImplementationPropsMarker::CallRet(..) => {
                        self::special_call_ret::apply_specialized_call_ret(
                            cs,
                            current_state,
                            common_opcode_state,
                            opcode_carry_parts,
                            global_context,
                            optimizer,
                            round_function,
                            witness_oracle,
                        )?
                    }
                };

                let OpcodePartialApplicationResult {
                    marker: _,
                    applies,
                    pending_sponges,
                    dst0_value,
                    dst1_value,
                    flags,
                    specific_registers_updates,
                    zero_out_specific_registers,
                    remove_ptr_on_specific_registers,
                    pending_exception,
                    callstack,
                    ergs_left,
                    new_pc,
                    new_ergs_per_pubdata_byte,
                    new_tx_number_in_block,
                    new_forward_queue_state,
                    new_forward_queue_length,
                    new_rollback_queue_state,
                    new_rollback_queue_length,
                    update_decommittment_queue,
                    new_decommittment_queue_state,
                    new_decommittment_queue_length,
                    new_memory_pages_counter,
                    new_did_call_or_ret_recently,
                    context_u128_new_value,
                    new_memory_queue_state,
                    new_memory_queue_length,
                    pending_arithmetic_operations,
                    new_heap_upper_bound,
                    new_aux_heap_upper_bound,
                } = spec_result;

                let result = OpcodePartialApplicationResult {
                    marker: self.clone(),
                    applies,
                    pending_sponges,
                    dst0_value,
                    dst1_value,
                    flags,
                    specific_registers_updates,
                    zero_out_specific_registers,
                    remove_ptr_on_specific_registers,
                    pending_exception,
                    callstack,
                    ergs_left,
                    new_pc,
                    new_ergs_per_pubdata_byte,
                    new_tx_number_in_block,
                    new_forward_queue_state,
                    new_forward_queue_length,
                    new_rollback_queue_state,
                    new_rollback_queue_length,
                    update_decommittment_queue,
                    new_decommittment_queue_state,
                    new_decommittment_queue_length,
                    new_memory_pages_counter,
                    new_did_call_or_ret_recently,
                    context_u128_new_value,
                    new_memory_queue_state,
                    new_memory_queue_length,
                    pending_arithmetic_operations,
                    new_heap_upper_bound,
                    new_aux_heap_upper_bound,
                };

                Ok(result)
            }
            _ => unimplemented!(),
        }
    }
}
