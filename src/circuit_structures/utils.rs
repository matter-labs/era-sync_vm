use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;

use super::*;

use super::*;
pub use crate::utils::*;
use franklin_crypto::plonk::circuit::bigint::single_table_range_constraint::*;
use franklin_crypto::plonk::circuit::SomeArithmetizable;

#[track_caller]
pub fn can_not_be_false_if_flagged<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    condition: &Boolean,
    condition_must_be_valid: &Boolean,
) -> Result<(), SynthesisError> {
    // only forbidden combination is condition is false and condition_must_be_valid == true
    match (condition.get_value(), condition_must_be_valid.get_value()) {
        (Some(c), Some(f)) => {
            let valid = if f { c } else { true };
            assert!(
                valid,
                "condition is broken: condition = {}, while enforcing flag = {}",
                c, f
            );
        }
        _ => {}
    }

    let invalid = Boolean::and(cs, &condition.not(), &condition_must_be_valid)?;
    Boolean::enforce_equal(cs, &invalid, &Boolean::constant(false))?;

    Ok(())
}

#[track_caller]
pub fn constraint_bit_length<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    if cs
        .get_table(crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME)
        .is_ok()
    {
        return constraint_bit_length_assuming_8x8_table(cs, num, num_bits);
    }
    let chunks = match num {
        Num::Variable(var) => {
            if let Some(value) = var.get_value() {
                let bits = value.into_repr().num_bits() as usize;
                assert!(
                    bits <= num_bits,
                    "Variable value is {} ({} bits) for {} bits constraint",
                    value,
                    bits,
                    num_bits
                );
            }
            enforce_using_single_column_table(cs, &var, num_bits)?
        }
        Num::Constant(value) => {
            let bits = value.into_repr().num_bits() as usize;
            assert!(bits <= num_bits);
            todo!();
        }
    };

    Ok(chunks)
}

#[track_caller]
pub fn constraint_bit_length_for_shifted_variable<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
    shift: E::Fr,
    num_bits: usize,
) -> Result<(), SynthesisError> {
    match num {
        Num::Variable(var) => {
            if let Some(value) = var.get_value() {
                let mut val = value;
                val.mul_assign(&shift);
                let bits = val.into_repr().num_bits() as usize;
                assert!(bits <= num_bits, "Variable value after shift is {} ({} bits) for {} bits constraint. Original value is {} and shift is {}", val, bits, num_bits, value, shift);
            }
            enforce_using_single_column_table_for_shifted_variable(cs, &var, shift, num_bits)?;
        }
        Num::Constant(value) => {
            let mut val = *value;
            val.mul_assign(&shift);
            let bits = val.into_repr().num_bits() as usize;
            assert!(bits <= num_bits, "Variable value after shift is {} ({} bits) for {} bits constraint. Original value is {} and shift is {}", val, bits, num_bits, value, shift);
        }
    }
    Ok(())
}

#[track_caller]
pub fn constraint_bit_length_assuming_8x8_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    num: &Num<E>,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    constraint_bit_length_for_shifted_variable_assuming_8x8_table(cs, num, E::Fr::one(), num_bits)
}

#[track_caller]
pub fn constraint_bit_length_for_shifted_variable_assuming_8x8_table<
    E: Engine,
    CS: ConstraintSystem<E>,
>(
    cs: &mut CS,
    num: &Num<E>,
    shift: E::Fr,
    num_bits: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    match num {
        Num::Variable(var) => {
            if let Some(value) = var.get_value() {
                let mut val = value;
                val.mul_assign(&shift);
                let bits = val.into_repr().num_bits() as usize;
                assert!(bits <= num_bits, "Variable value after shift is {} ({} bits) for {} bits constraint. Original value is {} and shift is {}", val, bits, num_bits, value, shift);
            }
            let allocated_chunks = enforce_using_8x8_table_for_shifted_variable(
                cs,
                &var,
                shift,
                num_bits,
                VM_BITWISE_LOGICAL_OPS_TABLE_NAME,
            )?;
            let as_num: Vec<_> = allocated_chunks
                .into_iter()
                .map(|el| Num::Variable(el))
                .collect();

            Ok(as_num)
        }
        Num::Constant(value) => {
            let mut val = *value;
            val.mul_assign(&shift);
            let bits = val.into_repr().num_bits() as usize;
            assert!(bits <= num_bits, "Variable value after shift is {} ({} bits) for {} bits constraint. Original value is {} and shift is {}", val, bits, num_bits, value, shift);

            let mut half_num_chunks = bits / 16;
            if bits % 16 != 0 {
                half_num_chunks += 1;
            }
            let chunks = split_into_slices(&val, 8, half_num_chunks * 2);
            let as_num: Vec<_> = chunks.into_iter().map(|el| Num::Constant(el)).collect();

            Ok(as_num)
        }
    }
}

pub fn compare_nums<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    a: &[Num<E>],
    b: &[Num<E>],
) -> Result<Boolean, SynthesisError> {
    assert_eq!(a.len(), b.len());
    let mut tmp_bools = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let tmp = Num::equals(cs, &a, &b)?;
        tmp_bools.push(tmp);
    }

    use crate::vm::partitioner::smart_and;

    let eq = smart_and(cs, &tmp_bools)?;

    Ok(eq)
}

// enforces that this value is `num_bits`, where `num_bits` must be a multiple of 16
pub fn enforce_using_8x8_table_for_shifted_variable<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    shift: E::Fr,
    num_bits: usize,
    table_name: &'static str,
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    use franklin_crypto::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;
    use std::sync::Arc;

    // we ensure that var * shift <= N bits
    //let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(
        cs.get_table(table_name).is_ok(),
        "failed to get table {}",
        table_name
    );

    if num_bits <= 16 {
        return enforce_using_8x8_table_into_single_gate_for_shifted_variable(
            cs,
            to_constraint,
            shift,
            num_bits,
            table_name,
        );
    }

    let remainder_bits = num_bits % 16;
    if remainder_bits != 0 {
        if num_bits - remainder_bits + 16 <= E::Fr::CAPACITY as usize {
            // we can shift the variable further to the left
            let mut new_shift = shift;
            for _ in 0..(16 - remainder_bits) {
                new_shift.double();
            }
            let new_num_bits = num_bits - remainder_bits + 16;
            return enforce_using_8x8_table_for_shifted_variable(
                cs,
                to_constraint,
                new_shift,
                new_num_bits,
                table_name,
            );
        } else {
            unimplemented!("we can not shift the variable enough to fit into single field element");
        }
    }

    // only work with aligned case without extra gates to constraint the remainder
    assert!(num_bits % 16 == 0);

    let dummy_var = CS::get_dummy_variable();

    use franklin_crypto::bellman::plonk::better_better_cs::cs::MainGate;

    let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
    assert_eq!(
        next_term_range.len(),
        1,
        "for now works only if only one variable is accessible on the next step"
    );

    let next_step_coeff_idx = next_term_range
        .next()
        .expect("must give at least one index");

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut accumulation_shift = E::Fr::one();
    for _ in 0..8 {
        accumulation_shift.double();
    }

    let mut current_term_coeff = E::Fr::one();

    let num_gates_for_coarse_constraint = num_bits / 16;
    let num_slices = num_gates_for_coarse_constraint;

    // we constraint it in such a way that it's a multiple of 16 bits
    let value_to_constraint = to_constraint.get_value().map(|el| {
        let mut tmp = el;
        tmp.mul_assign(&shift);

        tmp
    });

    let slices = split_some_into_slices(value_to_constraint, 8, num_slices * 2);

    let mut it = slices.into_iter();

    let mut next_step_variable_from_previous_gate: Option<AllocatedNum<E>> = None;
    // we start at -to_constraint and add bit chunks to set it to 0
    let mut next_step_value = value_to_constraint.map(|el| {
        let mut tmp = el;
        tmp.negate();

        tmp
    });

    let table = cs.get_table(table_name)?;

    use crate::bellman::plonk::better_better_cs::cs::MainGateTerm;

    let mut allocated_chunks = vec![];

    for full_gate_idx in 0..num_gates_for_coarse_constraint {
        let mut term = MainGateTerm::<E>::new();
        let value_0 = it.next().unwrap();
        let value_1 = it.next().unwrap();
        let chunk_allocated_0 = AllocatedNum::alloc(cs, || Ok(*value_0.get()?))?;
        let chunk_allocated_1 = AllocatedNum::alloc(cs, || Ok(*value_1.get()?))?;

        let scaled_0 = value_0.mul(&Some(current_term_coeff));

        let mut coeff_1 = current_term_coeff;
        coeff_1.mul_assign(&accumulation_shift);
        let scaled_1 = value_1.mul(&Some(coeff_1));

        let contribution_from_this_row = scaled_0.add(&scaled_1);
        next_step_value = next_step_value.add(&contribution_from_this_row);

        let is_last_step = full_gate_idx == num_gates_for_coarse_constraint - 1;

        if is_last_step {
            if let Some(v) = next_step_value.clone() {
                assert!(v.is_zero());
            }
        }

        use crate::bellman::plonk::better_better_cs::cs::ArithmeticTerm;

        allocated_chunks.push(chunk_allocated_0);
        allocated_chunks.push(chunk_allocated_1);

        // + a * 2^k + b * 2^(k+8)
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(
            chunk_allocated_0.get_variable(),
            current_term_coeff,
        ));
        current_term_coeff.mul_assign(&accumulation_shift);

        term.add_assign(ArithmeticTerm::from_variable_and_coeff(
            chunk_allocated_1.get_variable(),
            current_term_coeff,
        ));
        current_term_coeff.mul_assign(&accumulation_shift);

        // add padding into C polys
        // for _ in 2..3 {
        //     term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(explicit_zero_var, E::Fr::zero()));
        // }

        let lookup_result_value =
            match (chunk_allocated_0.get_value(), chunk_allocated_1.get_value()) {
                (Some(k0), Some(k1)) => Some(table.query(&[k0, k1])?[0]),
                _ => None,
            };
        let placeholder_var = AllocatedNum::alloc(cs, || Ok(*lookup_result_value.get()?))?;
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(
            placeholder_var.get_variable(),
            E::Fr::zero(),
        ));

        // it's not a first gate, so we carry from the last round
        if let Some(from_previous) = next_step_variable_from_previous_gate.take() {
            if is_last_step {
                // we place +d here, and we expect no more d_next
                term.add_assign(ArithmeticTerm::from_variable(from_previous.get_variable()));
            } else {
                // expect +d here, but also we need some remainder for next row
                term.add_assign(ArithmeticTerm::from_variable(from_previous.get_variable()));
                let next_step_allocated = AllocatedNum::alloc(cs, || Ok(*next_step_value.get()?))?;

                next_step_variable_from_previous_gate = Some(next_step_allocated.clone());
            }
        } else {
            // first round we just place what we want to constraint shifted
            term.sub_assign(ArithmeticTerm::from_variable_and_coeff(
                to_constraint.get_variable(),
                shift,
            ));
            let next_step_allocated = AllocatedNum::alloc(cs, || Ok(*next_step_value.get()?))?;

            next_step_variable_from_previous_gate = Some(next_step_allocated.clone());
        }

        // format taking into account the duplicates exist
        let (variables, mut coeffs) =
            CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;
        if !is_last_step {
            coeffs[next_step_coeff_idx] = minus_one;
        }

        cs.begin_gates_batch_for_step()?;

        cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &variables, &[])?;

        cs.apply_single_lookup_gate(&variables[0..3], Arc::clone(&table))?;

        cs.end_gates_batch_for_step()?;
    }

    Ok(allocated_chunks)
}

// enforces that this value * shift is exactly `num_bits` long
fn enforce_using_8x8_table_into_single_gate_for_shifted_variable<
    E: Engine,
    CS: ConstraintSystem<E>,
>(
    cs: &mut CS,
    to_constraint: &AllocatedNum<E>,
    shift: E::Fr,
    num_bits: usize,
    table_name: &'static str,
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    use franklin_crypto::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;

    // let strategies = get_range_constraint_info(&*cs);
    // assert_eq!(CS::Params::STATE_WIDTH, 4);
    // assert!(strategies.len() > 0);
    // assert!(strategies[0].strategy == RangeConstraintStrategy::SingleTableInvocation);

    assert!(num_bits <= 16);

    let table = cs.get_table(table_name)?;

    let dummy_var = CS::get_dummy_variable();

    let mut shift = shift;
    for _ in 0..(16 - num_bits) {
        shift.double();
    }

    let mut shift_8 = E::Fr::one();
    for _ in 0..8 {
        shift_8.double();
    }

    use crate::bellman::plonk::better_better_cs::cs::MainGateTerm;

    let mut term = MainGateTerm::<E>::new();
    let shifted_value = to_constraint.get_value().map(|el| {
        let mut tmp = el;
        tmp.mul_assign(&shift);

        tmp
    });

    // split into chunks
    let chunks = split_some_into_fixed_number_of_limbs(some_fe_to_biguint(&shifted_value), 8, 2);
    let chunks: Vec<Option<E::Fr>> = chunks
        .into_iter()
        .map(|el| el.map(|e| biguint_to_fe(e)))
        .collect();
    assert_eq!(chunks.len(), 2);
    let val_0 = chunks[0];
    let val_1 = chunks[1];

    let allocated_0 = AllocatedNum::alloc(cs, || Ok(*val_0.get()?))?;
    let allocated_1 = AllocatedNum::alloc(cs, || Ok(*val_1.get()?))?;

    use crate::bellman::plonk::better_better_cs::cs::ArithmeticTerm;

    term.add_assign(ArithmeticTerm::from_variable(allocated_0.get_variable()));
    term.add_assign(ArithmeticTerm::from_variable_and_coeff(
        allocated_1.get_variable(),
        shift_8,
    ));

    // for _ in 2..3 {
    //     term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(explicit_zero_var, E::Fr::zero()));
    // }

    let lookup_result_value = match (allocated_0.get_value(), allocated_1.get_value()) {
        (Some(k0), Some(k1)) => Some(table.query(&[k0, k1])?[0]),
        _ => None,
    };
    let placeholder_var = AllocatedNum::alloc(cs, || Ok(*lookup_result_value.get()?))?;
    term.add_assign(ArithmeticTerm::from_variable_and_coeff(
        placeholder_var.get_variable(),
        E::Fr::zero(),
    ));

    term.sub_assign(ArithmeticTerm::from_variable_and_coeff(
        to_constraint.get_variable(),
        shift,
    ));

    use franklin_crypto::bellman::plonk::better_better_cs::cs::MainGate;

    let (variables, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;

    cs.begin_gates_batch_for_step()?;

    cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &variables, &[])?;

    cs.apply_single_lookup_gate(&variables[0..3], table)?;

    cs.end_gates_batch_for_step()?;

    Ok(vec![allocated_0, allocated_1])
}

// uses 8x8 table to range check two bytes
fn range_check_two_u8_using_8x8_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    to_constraint: [AllocatedNum<E>; 2],
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    use franklin_crypto::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;
    let table = cs.get_table(crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME)?;

    let dummy_var = CS::get_dummy_variable();

    use crate::bellman::plonk::better_better_cs::cs::MainGateTerm;

    let mut term = MainGateTerm::<E>::new();

    let [allocated_0, allocated_1] = to_constraint;

    use crate::bellman::plonk::better_better_cs::cs::ArithmeticTerm;

    term.add_assign(ArithmeticTerm::from_variable_and_coeff(
        allocated_0.get_variable(),
        E::Fr::zero(),
    ));
    term.add_assign(ArithmeticTerm::from_variable_and_coeff(
        allocated_1.get_variable(),
        E::Fr::zero(),
    ));

    let lookup_result_value = match (allocated_0.get_value(), allocated_1.get_value()) {
        (Some(k0), Some(k1)) => Some(table.query(&[k0, k1])?[0]),
        _ => None,
    };
    let placeholder_var = AllocatedNum::alloc(cs, || Ok(*lookup_result_value.get()?))?;
    term.add_assign(ArithmeticTerm::from_variable_and_coeff(
        placeholder_var.get_variable(),
        E::Fr::zero(),
    ));
    term.add_assign_allowing_duplicates(ArithmeticTerm::from_variable_and_coeff(
        dummy_var,
        E::Fr::zero(),
    ));

    use franklin_crypto::bellman::plonk::better_better_cs::cs::MainGate;

    let (variables, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;

    cs.begin_gates_batch_for_step()?;

    cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &variables, &[])?;

    cs.apply_single_lookup_gate(&variables[0..3], table)?;

    cs.end_gates_batch_for_step()?;

    Ok(vec![allocated_0, allocated_1])
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::testing::*;

    use crate::pairing::bn256::*;

    #[test]
    fn test_new_range_check_gates() -> Result<(), SynthesisError> {
        let witness = 1u128 << 79;
        let witness = Fr::from_str(&witness.to_string()).unwrap();

        let (mut dummy_cs, _, _) = create_test_artifacts_with_optimized_gate();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let witness = Num::alloc(cs, Some(witness))?;

        // We need to allocate a zero var here, otherwise our counting is not precise

        let _ = cs.get_explicit_zero()?;

        let n = cs.get_current_step_number();
        enforce_using_single_column_table_for_shifted_variable_optimized(
            cs,
            &witness.get_variable(),
            Fr::one(),
            92,
        )?;
        println!(
            "Using {} gates for optimized case",
            cs.get_current_step_number() - n
        );

        let n = cs.get_current_step_number();
        enforce_using_single_column_table_for_shifted_variable(
            cs,
            &witness.get_variable(),
            Fr::one(),
            92,
        )?;
        println!(
            "Using {} gates for non-optimized case",
            cs.get_current_step_number() - n
        );

        assert!(cs.is_satisfied());

        Ok(())
    }
}
