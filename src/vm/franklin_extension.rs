use super::*;
use crate::bellman::pairing::Engine;

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, ConstraintSystem, MainGate, MainGateTerm, Variable,
};

// asserts that flag * num is always zero
pub fn conditionally_enforce_zero<E, CS>(
    cs: &mut CS,
    flag: &Boolean,
    num: &Num<E>,
) -> Result<(), SynthesisError>
where
    E: Engine,
    CS: ConstraintSystem<E>,
{
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    match (flag, num) {
        (Boolean::Constant(flag), Num::Constant(fr)) => assert!(!flag || fr.is_zero()),
        (Boolean::Constant(flag), Num::Variable(var)) => {
            if *flag {
                let lc = LinearCombination::from(var.clone());
                lc.enforce_zero(cs)?;
            }
        }
        (Boolean::Is(flag), Num::Constant(fr)) => {
            if !fr.is_zero() {
                let mut lc = LinearCombination::zero();
                lc.add_assign_bit_with_coeff(flag, E::Fr::one());
                lc.enforce_zero(cs)?;
            }
        }
        (Boolean::Not(flag), Num::Constant(fr)) => {
            if !fr.is_zero() {
                let mut lc = LinearCombination::zero();
                lc.add_assign_bit_with_coeff(flag, E::Fr::one());
                lc.add_assign_constant(minus_one.clone());
                lc.enforce_zero(cs)?;
            }
        }
        (Boolean::Is(flag), Num::Variable(var)) => {
            let mut gate = MainGateTerm::new();
            let term = ArithmeticTerm::from_variable(flag.get_variable())
                .mul_by_variable(var.get_variable());
            gate.add_assign(term);
            cs.allocate_main_gate(gate)?;
        }
        (Boolean::Not(flag), Num::Variable(var)) => {
            // 0 = var (flag - 1) = var * flag - var;
            let mut gate = MainGateTerm::new();
            let term = ArithmeticTerm::from_variable(flag.get_variable())
                .mul_by_variable(var.get_variable());
            gate.add_assign(term);
            let term = ArithmeticTerm::from_variable(var.get_variable());
            gate.sub_assign(term);
            cs.allocate_main_gate(gate)?;
        }
    }

    Ok(())
}
