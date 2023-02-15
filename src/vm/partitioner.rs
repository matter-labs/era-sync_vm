use super::structural_eq::*;
use super::*;

pub fn smart_or<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bools: &[Boolean],
) -> Result<Boolean, SynthesisError> {
    const LIMIT: usize = 4;
    if bools.len() == 0 {
        return Ok(Boolean::constant(false));
    }

    if bools.len() == 1 {
        return Ok(bools[0]);
    }

    if bools.len() == 2 {
        // 1 gate
        let result = Boolean::or(cs, &bools[0], &bools[1])?;
        return Ok(result);
    }

    // 1 gate for 2,
    // 2 gates for 3, etc
    if bools.len() < LIMIT {
        // 1 gate
        let mut result = Boolean::or(cs, &bools[0], &bools[1])?;
        // len - 2 gates
        for b in bools[2..].iter() {
            result = Boolean::or(cs, &result, &b)?;
        }
        return Ok(result);
    }

    // 1 gate for 3
    // 2 gates for 6
    // 3 gates for 9, etc
    let mut lc = LinearCombination::zero();
    for b in bools.iter() {
        lc.add_assign_boolean_with_coeff(b, E::Fr::one());
    }
    let as_num = lc.into_num(cs)?;

    // 2 gates here
    let all_false = as_num.is_zero(cs)?;

    // so 2 gates for 3
    // 4 gates for 6
    // 5 gates for 9
    // so we win at 4+

    Ok(all_false.not())
}

pub fn smart_and<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    bools: &[Boolean],
) -> Result<Boolean, SynthesisError> {
    const LIMIT: usize = 4;
    assert!(bools.len() > 0);
    if bools.len() == 1 {
        return Ok(bools[0]);
    }

    if bools.len() == 2 {
        // 1 gate
        let result = Boolean::and(cs, &bools[0], &bools[1])?;
        return Ok(result);
    }

    // 1 gate for 2,
    // 2 gates for 3, etc
    if bools.len() < LIMIT {
        // 1 gate
        let mut result = Boolean::and(cs, &bools[0], &bools[1])?;
        // len - 2 gates
        for b in bools[2..].iter() {
            result = Boolean::and(cs, &result, &b)?;
        }
        return Ok(result);
    }

    // 1 gate for 3
    // 2 gates for 6
    // 3 gates for 9, etc
    let mut lc = LinearCombination::zero();
    let num_elements_as_fr = E::Fr::from_str(&bools.len().to_string()).unwrap();
    lc.sub_assign_constant(num_elements_as_fr);
    for b in bools.iter() {
        lc.add_assign_boolean_with_coeff(b, E::Fr::one());
    }
    let as_num = lc.into_num(cs)?;

    // 2 gates here
    let all_true = as_num.is_zero(cs)?;

    // so 2 gates for 3
    // 4 gates for 6
    // 5 gates for 9
    // so we win at 4+

    Ok(all_true)
}

pub(crate) fn partition<E: Engine, T: Clone + CircuitEq<E> + CircuitOrd<E>, B: Clone>(
    baseline: &T,
    variants: &[(B, T)],
) -> (Vec<B>, Vec<(Vec<B>, T)>) {
    let mut baseline_equal = vec![];
    let mut nontrivial_variants = vec![];
    for (_idx, (flag, variant)) in variants.iter().enumerate() {
        if variant.eq(baseline) {
            baseline_equal.push(flag.clone());
        } else {
            nontrivial_variants.push((flag.clone(), variant.clone()))
        }
    }

    let mut nontrivial_variants_partitioned = vec![];
    nontrivial_variants.sort_by(|a, b| a.1.cmp(&b.1));

    let mut previous: Option<T> = None;
    let mut partition = vec![];
    for variant in nontrivial_variants.into_iter() {
        if let Some(prev) = previous.take() {
            if prev.eq(&variant.1) {
                partition.push(variant.0);
                previous = Some(prev);
            } else {
                let previous_partition = std::mem::replace(&mut partition, vec![]);
                nontrivial_variants_partitioned.push((previous_partition, prev.clone()));
                previous = Some(variant.1);
                partition.push(variant.0);
            }
        } else {
            previous = Some(variant.1);
            partition.push(variant.0);
        }
    }

    if partition.len() != 0 {
        nontrivial_variants_partitioned.push((partition, previous.take().expect("must be some")));
    }

    nontrivial_variants_partitioned.sort_by(|a, b| b.0.len().cmp(&a.0.len()));

    (baseline_equal, nontrivial_variants_partitioned)
}

pub(crate) fn select_update_assuming_orthogonality<
    E: Engine,
    CS: ConstraintSystem<E>,
    T: Clone + CircuitEq<E> + CircuitOrd<E> + CircuitSelectable<E>,
>(
    cs: &mut CS,
    reference: T,
    candidates: &[(Boolean, T)],
) -> Result<T, SynthesisError> {
    let (_, partitions) = partition(&reference, &candidates);
    let mut new = reference;
    for (flags, value) in partitions.into_iter() {
        let flag = smart_or(cs, &flags)?;
        new = T::conditionally_select(cs, &flag, &value, &new)?;
    }

    Ok(new)
}
