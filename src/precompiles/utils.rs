use super::*;

use crate::franklin_crypto::bellman::plonk::better_better_cs::cs::LookupTableApplication;

pub fn table_width_3_lookup<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    table_name: &str,
    logical_input: &[Num<E>],
) -> Result<Vec<Num<E>>, SynthesisError> {
    assert!(logical_input.len() > 0);
    assert!(logical_input.len() <= 3);

    let table = cs.get_table(table_name)?;

    let mut flattened_variables = vec![];

    let mut inputs_tmp = Some(vec![]);
    for el in logical_input.iter() {
        assert!(!el.is_constant());
        flattened_variables.push(el.get_variable().get_variable());
        if let Some(value) = el.get_value() {
            if let Some(inputs) = inputs_tmp.as_mut() {
                inputs.push(value);
            }
        } else {
            inputs_tmp = None;
        }
    }

    // perform a lookup
    let outputs_witness = if let Some(inputs) = inputs_tmp.as_ref() {
        let out = table.query(&inputs[..])?;
        Some(out)
    } else {
        None
    };

    let num_outputs = 3 - logical_input.len();

    let mut outputs = vec![];

    for i in 0..num_outputs {
        let witness = outputs_witness.as_ref().map(|el| el[i]);
        let num = Num::alloc(cs, witness)?;
        flattened_variables.push(num.get_variable().get_variable());
        outputs.push(num);
    }

    // create gate

    let gate_term = MainGateTerm::new();
    let dummy = AllocatedNum::zero(cs).get_variable();
    let (mut gate_vars, gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
    gate_vars[0..3].copy_from_slice(&flattened_variables);

    // our gate is 0*0 + 0 + 0 + ... = 0
    // but there exists a table relationship

    cs.begin_gates_batch_for_step()?;
    cs.apply_single_lookup_gate(&flattened_variables, table.clone())?;
    cs.new_gate_in_batch(&CS::MainGate::default(), &gate_coefs, &gate_vars, &[])?;
    cs.end_gates_batch_for_step()?;

    Ok(outputs)
}
