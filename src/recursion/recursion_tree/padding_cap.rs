use super::*;

use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;

// we assume a circuit geometry to be in some form
// and we want all polynomials to be strictly non-zero
pub fn add_padding_cap<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
) -> Result<(), SynthesisError> {
    // utilize at least one lookup table
    let _ = UInt16::allocate(cs, Some(1u16))?;
    // utilize main gate and D_next selector
    let mut lc = LinearCombination::zero();
    lc.add_assign_constant(E::Fr::one());
    for i in 0..CS::Params::STATE_WIDTH * 2 {
        let var = Num::alloc(cs, Some(u64_to_fe(i as u64)))?;
        lc.add_assign_number_with_coeff(&var, E::Fr::one());
    }
    let _ = lc.into_num(cs)?;
    // use bi-quadratic main gate just in case
    let boolean = Boolean::alloc(cs, Some(true))?;
    let a = Num::alloc(cs, Some(u64_to_fe(42u64)))?;
    let b = Num::alloc(cs, Some(E::Fr::zero()))?;
    let _ = Num::conditionally_select(cs, &boolean, &a, &b)?;
    // use 5th degree non-linearity gate
    let _ = crate::franklin_crypto::plonk::circuit::custom_rescue_gate::apply_5th_power(
        cs,
        &a.get_variable(),
        None,
    )?;

    Ok(())
}
