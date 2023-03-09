use super::*;

use crate::vm::vm_cycle::final_state_merging::merge_into_next_state;
use crate::vm::vm_cycle::pre_state::*;
use crate::vm::vm_cycle::witness_oracle::WitnessOracle;
use crate::vm::vm_state::GlobalContext;
use crate::vm::vm_state::{VmGlobalState, VmLocalState};

pub fn vm_cycle<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: VmLocalState<E, 3>,
    witness_oracle: &mut impl WitnessOracle<E>,
    round_function: &R,
    global_context: &GlobalContext<E>,
) -> Result<VmLocalState<E, 3>, SynthesisError> {
    // decide on opcode and initial exceptions

    let (new_state, common_opcode_state, opcode_carry_parts) =
        create_prestate(cs, current_state, witness_oracle, round_function)?;

    // now apply every individual opcode from the markers set

    let mut opcode_partial_results = vec![];

    let mut ctx = OptimizationContext::empty();

    // we modified a state just enough to properly capture small properties changes like PC and SP

    for marker in ALL_OPCODE_MARKERS.iter() {
        use crate::vm::vm_cycle::pre_state::InCircuitOpcode;

        let result = marker.apply(
            cs,
            &new_state,
            &common_opcode_state,
            &opcode_carry_parts,
            global_context,
            &mut ctx,
            round_function,
            witness_oracle,
        )?;

        opcode_partial_results.push(result);
    }

    // enforce optimizer

    let n = cs.get_current_aux_gate_number();

    let nn = cs.get_current_aux_gate_number();
    ctx.enforce_addsub_algebraic_relationships(cs)?;
    let _gates_used = cs.get_current_aux_gate_number() - nn;
    let _message = format!("{} gates used for add/sub optimizer", _gates_used);
    // dbg!(_message);

    let nn = cs.get_current_aux_gate_number();
    ctx.enforce_divmul_algebraic_relationships(cs)?;
    let _gates_used = cs.get_current_aux_gate_number() - nn;
    let _message = format!("{} gates used for div/mul optimizer", _gates_used);
    // dbg!(_message);

    let nn = cs.get_current_aux_gate_number();
    ctx.enforce_zero_checks(cs)?;
    let _gates_used = cs.get_current_aux_gate_number() - nn;
    let _message = format!("{} gates used for zero-checks optimizer", _gates_used);
    // dbg!(_message);

    let nn = cs.get_current_aux_gate_number();
    ctx.enforce_unconditional_range_checks(cs)?;
    let _gates_used = cs.get_current_aux_gate_number() - nn;
    let _message = format!(
        "{} gates used for unconditional range checks optimizer",
        _gates_used
    );
    // dbg!(_message);

    let nn = cs.get_current_aux_gate_number();
    ctx.enforce_conditional_range_checks(cs)?;
    let _gates_used = cs.get_current_aux_gate_number() - nn;
    let _message = format!(
        "{} gates used for conditional range checks optimizer",
        _gates_used
    );
    // dbg!(_message);

    // Boolean constraints my be the last ones
    let nn = cs.get_current_aux_gate_number();
    ctx.enforce_boolean_allocations(cs)?;
    let _gates_used = cs.get_current_aux_gate_number() - nn;
    let _message = format!(
        "{} gates used for booleanity constraint optimizer",
        _gates_used
    );
    // dbg!(_message);

    drop(ctx);

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for optimizer", gates_used);
    // dbg!(_message);

    // and just merge it

    let new_state = merge_into_next_state(
        cs,
        new_state,
        opcode_carry_parts,
        opcode_partial_results,
        round_function,
        witness_oracle,
    )?;

    Ok(new_state)
}

// this is the very last cycle of VM which is responsible for processing all pendings (if there are any)
// this cylce will never start execution of a new instruction, and is effectively and execution of NOP
// coming from nowhere
pub fn vm_process_pending<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: VmLocalState<E, 3>,
    round_function: &R,
) -> Result<VmGlobalState<E, 3>, SynthesisError> {
    let (global_state, pended_rfs, pended_algebraic_rels) = current_state.split();
    // first we should finalize all pending sponges
    for request in pended_rfs.records.into_iter().flatten() {
        let true_final_state = round_function.round_function(cs, request.initial_state)?;
        for (a, b) in request
            .final_state
            .into_iter()
            .zip(true_final_state.into_iter())
        {
            Num::conditionally_enforce_equal(cs, &request.is_used, &a, &b)?;
        }
    }

    assert!(pended_algebraic_rels.is_empty());

    // now deal with pended algebraic operations:
    let mut opt_ctx = OptimizationContext::empty();
    let marker = CtxMarker::pending_marker();
    for (relation, applies) in pended_algebraic_rels.into_iter() {
        match relation {
            PendingArithmeticRelation::AddSubRelation(rel) => {
                opt_ctx.uint256_addsub_tuples.push((marker, applies, rel))
            }
            PendingArithmeticRelation::MulDivRelation(rel) => {
                opt_ctx.uint256_divmul_tuples.push((marker, applies, rel))
            }
            PendingArithmeticRelation::RangeCheckRelation(rel) => {
                opt_ctx.add_range_check(cs, &rel.0, applies, marker, rel.1)?
            }
        };
    }
    opt_ctx.enforce_addsub_algebraic_relationships(cs)?;
    opt_ctx.enforce_divmul_algebraic_relationships(cs)?;
    opt_ctx.enforce_zero_checks(cs)?;
    opt_ctx.enforce_unconditional_range_checks(cs)?;
    opt_ctx.enforce_conditional_range_checks(cs)?;

    // VM doesn't bump timestamp on skips / pending ops

    Ok(global_state)
}
