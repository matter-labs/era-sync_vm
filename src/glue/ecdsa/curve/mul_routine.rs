use super::*;
use super::curve::*;
use super::mul_table::*;
use franklin_crypto::plonk::circuit::bigint::*;
use franklin_crypto::plonk::circuit::curve::*;
use super::decomposition::*;

use std::convert::TryInto;


pub(crate) fn create_info<E: Engine, F: PrimeField>(el: FieldElement<'_, E, F>) -> (Vec<Num<E>>, Vec<usize>) {
    let mut limbs = vec![];
    for l in el.binary_limbs.into_iter() {
        let num = l.term.into_num();
        limbs.push(num);
    }
    let widths =  el.representation_params.binary_limbs_bit_widths.clone();

    (limbs, widths)
}

// supply scalar decomposition from the most significant to least significant chunk
pub fn mul_fixed_point_by_variable_scalar<
    'a, 
    E: Engine, 
    CS: ConstraintSystem<E>,
    G: GenericCurveAffine,
    const N: usize,
>(
    cs: &mut CS,
    base: G,
    scalar_window_width: usize, 
    rns_params: &'a RnsParameters<E, G::Base>,
    scalar_decomposition: &[UInt16<E>]
) -> Result<AffinePoint<'a, E, G>, SynthesisError> where G::Base: PrimeField {
    assert!(scalar_window_width <= 16);
    assert_eq!(N, rns_params.num_binary_limbs * 2);

    let mut mul_table = MulTable::<_, _, N>::new_for_fixed_point(base, scalar_window_width, rns_params);
    
    let result = mul_by_variable_scalar_with_shared_table(
        cs,
        rns_params,
        scalar_decomposition,
        &mut mul_table
    )?;

    mul_table.enforce_validity_optimized(cs)?;

    Ok(result)
}

// supply scalar decomposition from the most significant to least significant chunk
#[track_caller]
pub fn mul_by_variable_scalar_with_shared_table<
    'a, 
    E: Engine, 
    CS: ConstraintSystem<E>,
    G: GenericCurveAffine,
    const N: usize,
>(
    cs: &mut CS,
    rns_params: &'a RnsParameters<E, G::Base>,
    scalar_decomposition: &[UInt16<E>],
    mul_table: &mut MulTable<E, G, N>
) -> Result<AffinePoint<'a, E, G>, SynthesisError> where G::Base: PrimeField {
    let scalar_window_width = mul_table.window_width;
    assert!(scalar_window_width <= 16);
    assert_eq!(N, rns_params.num_binary_limbs * 2);

    let random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log_generic::<G::Projective>(b"FIXED_BASE_DST", 1)[0];
    let mut compensation = random_point.into_projective();
    let random_point = AffinePoint::constant(random_point, rns_params);

    let mut result = random_point.clone();
    // first window without doubling
    let chunk = scalar_decomposition[0];
    let chunk_is_zero = chunk.is_zero(cs)?;
    // query a chunk
    let chunk = mul_table.read(cs, chunk)?;
    // cast to the point
    let (x_coordinate, y_coordinate) = chunk.split_at(N/2);
    let x = FieldElement::from_single_limb_witnesses_unchecked(cs, &x_coordinate, rns_params)?;
    let y = FieldElement::from_single_limb_witnesses_unchecked(cs, &y_coordinate, rns_params)?;

    let point = AffinePoint::<_, G>::from_xy_unchecked(x, y);
    let (intermediate, (tmp, _)) = result.add_unequal_unchecked(cs, point)?;
    let (intermediate, _) = AffinePoint::select(cs, &chunk_is_zero, tmp, intermediate)?;
    result = intermediate;

    let full_rounds = scalar_decomposition.len();
    for i in 1..full_rounds {
        // double enough times
        for _ in 0..scalar_window_width {
            let (tmp, _) = result.double(cs)?;
            result = tmp;
            compensation.double();
        }
        // now add a chunk
        let chunk = scalar_decomposition[i];
        let chunk_is_zero = chunk.is_zero(cs)?;
        // query a chunk
        let chunk = mul_table.read(cs, chunk)?;
        // cast to the point
        let (x_coordinate, y_coordinate) = chunk.split_at(N/2);
        let x = FieldElement::from_single_limb_witnesses_unchecked(cs, &x_coordinate, rns_params)?;
        let y = FieldElement::from_single_limb_witnesses_unchecked(cs, &y_coordinate, rns_params)?;

        let point = AffinePoint::<_, G>::from_xy_unchecked(x, y);
        let (intermediate, (tmp, _)) = result.add_unequal_unchecked(cs, point)?;
        let (intermediate, _) = AffinePoint::select(cs, &chunk_is_zero, tmp, intermediate)?;
        result = intermediate;
    }

    // subtract enough contributions of the random point
    let compensation = AffinePoint::constant(compensation.into_affine(), rns_params);
    let (result, _) = result.sub_unequal(cs, compensation)?;

    Ok(result)
}

// supply scalar decomposition from the most significant to least significant chunk
pub fn signed_mul_fixed_point_by_variable_scalar<
    'a, 
    E: Engine, 
    CS: ConstraintSystem<E>,
    G: GenericCurveAffine,
    const N: usize,
>(
    cs: &mut CS,
    base: G,
    window_width: usize, 
    rns_params: &'a RnsParameters<E, G::Base>,
    scalar_decomposition: &[(Boolean, UInt16<E>)]
) -> Result<AffinePoint<'a, E, G>, SynthesisError> where G::Base: PrimeField {
    assert!(window_width <= 16);
    assert_eq!(N, rns_params.num_binary_limbs * 2);

    let mut mul_table = MulTable::<_, _, N>::new_signed_for_fixed_point(base, window_width, rns_params);
    
    let result = signed_mul_by_variable_scalar_with_shared_table(
        cs,
        rns_params,
        scalar_decomposition,
        &mut mul_table
    )?;

    mul_table.enforce_validity_optimized(cs)?;

    Ok(result)
}

// supply scalar decomposition from the most significant to least significant chunk
pub fn signed_mul_by_variable_scalar_with_shared_table<
    'a, 
    E: Engine, 
    CS: ConstraintSystem<E>,
    G: GenericCurveAffine,
    const N: usize,
>(
    cs: &mut CS,
    rns_params: &'a RnsParameters<E, G::Base>,
    scalar_decomposition: &[(Boolean, UInt16<E>)],
    mul_table: &mut MulTable::<E, G, N>,
) -> Result<AffinePoint<'a, E, G>, SynthesisError> where G::Base: PrimeField {
    let window_width = mul_table.window_width;
    assert_eq!(N, rns_params.num_binary_limbs * 2);

    let random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log_generic::<G::Projective>(b"FIXED_BASE_DST", 1)[0];
    let mut compensation = random_point.into_projective();
    let random_point = AffinePoint::constant(random_point, rns_params);

    let mut result = random_point.clone();
    // first window without doubling
    let (flag, chunk) = scalar_decomposition[0];
    let chunk_is_zero = chunk.is_zero(cs)?;
    // query a chunk
    let chunk = mul_table.read(cs, chunk)?;
    // cast to the point
    let (x_coordinate, y_coordinate) = chunk.split_at(N/2);
    let x = FieldElement::from_single_limb_witnesses_unchecked(cs, &x_coordinate, rns_params)?;
    let y = FieldElement::from_single_limb_witnesses_unchecked(cs, &y_coordinate, rns_params)?;

    let point = AffinePoint::<_, G>::from_xy_unchecked(x, y);
    let (point, _) = point.conditionally_negate(cs, &flag)?;

    let (intermediate, (tmp, _)) = result.add_unequal_unchecked(cs, point)?;
    let (mut intermediate, _) = AffinePoint::select(cs, &chunk_is_zero, tmp, intermediate)?;
    result = intermediate;

    let full_rounds = scalar_decomposition.len();
    for i in 1..full_rounds {
        // double enough times
        for _ in 0..window_width {
            let (tmp, _) = result.double(cs)?;
            result = tmp;
            compensation.double();
        }
        // now add a chunk
        let (flag, chunk) = scalar_decomposition[i];
        let chunk_is_zero = chunk.is_zero(cs)?;
        // query a chunk
        let chunk = mul_table.read(cs, chunk)?;
        // cast to the point
        let (x_coordinate, y_coordinate) = chunk.split_at(N/2);
        let x = FieldElement::from_single_limb_witnesses_unchecked(cs, &x_coordinate, rns_params)?;
        let y = FieldElement::from_single_limb_witnesses_unchecked(cs, &y_coordinate, rns_params)?;

        let point = AffinePoint::<_, G>::from_xy_unchecked(x, y);
        let (point, _) = point.conditionally_negate(cs, &flag)?;
        let (intermediate, (tmp, _)) = result.add_unequal_unchecked(cs, point)?;
        let (intermediate, _) = AffinePoint::select(cs, &chunk_is_zero, tmp, intermediate)?;
        result = intermediate;
    }

    // subtract enough contributions of the random point
    let compensation = AffinePoint::constant(compensation.into_affine(), rns_params);
    let (result, _) = result.sub_unequal(cs, compensation)?;

    Ok(result)
}

// supply scalar decomposition from the most significant to least significant chunk
pub fn mul_variable_point_by_variable_scalar<
    'a, 
    E: Engine, 
    CS: ConstraintSystem<E>,
    G: GenericCurveAffine,
    const N: usize,
>(
    cs: &mut CS,
    base: AffinePoint<'a, E, G>,
    window_width: usize, 
    rns_params: &'a RnsParameters<E, G::Base>,
    scalar_decomposition: &[UInt16<E>]
) -> Result<AffinePoint<'a, E, G>, SynthesisError> where G::Base: PrimeField {
    println!("Variable base multiplication with width {}", window_width);
    assert!(window_width <= 16);
    assert_eq!(N, rns_params.num_binary_limbs * 2);

    let mut mul_table = MulTable::<_, _, N>::new_for_variable_point(cs, base, window_width, rns_params)?;

    let result = mul_by_variable_scalar_with_shared_table(
        cs,
        rns_params,
        scalar_decomposition,
        &mut mul_table
    )?;

    mul_table.enforce_validity_optimized(cs)?;

    Ok(result)
}

// supply scalar decomposition from the most significant to least significant chunk
pub fn signed_mul_variable_point_by_variable_scalar<
    'a, 
    E: Engine, 
    CS: ConstraintSystem<E>,
    G: GenericCurveAffine,
    const N: usize,
>(
    cs: &mut CS,
    base: AffinePoint<'a, E, G>,
    window_width: usize, 
    rns_params: &'a RnsParameters<E, G::Base>,
    scalar_decomposition: &[(Boolean, UInt16<E>)]
) -> Result<AffinePoint<'a, E, G>, SynthesisError> where G::Base: PrimeField {
    println!("Signed variable base multiplication with width {}", window_width);
    assert!(window_width <= 16);
    assert_eq!(N, rns_params.num_binary_limbs * 2);

    let mut mul_table = MulTable::<_, _, N>::new_signed_for_variable_point(cs, base, window_width, rns_params)?;

    let result = signed_mul_by_variable_scalar_with_shared_table(
        cs,
        rns_params,
        scalar_decomposition,
        &mut mul_table
    )?;

    mul_table.enforce_validity_optimized(cs)?;

    Ok(result)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::testing::*;

    type E = Bn256;

    use super::super::fq::Fq;
    use super::super::fr::Fr as FrSecp256;

    #[test]
    fn test_fixed_base_multiplication() -> Result<(), SynthesisError> {
        let rns_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let scalar_bits = 256;

        let widths = vec![3, 4, 5, 6, 7, 8];
        for width in widths {
            let mask = (1<<width) - 1;
            let mut windows = vec![];
            let mut remaining = scalar_bits;
            let mut rng = crate::testing::deterministic_rng();

            loop {
                if remaining > width {
                    remaining -= width;
                    let value = rng.gen::<usize>() & mask;
                    windows.push(value);
                } else {
                    let value = rng.gen::<usize>() & mask;
                    windows.push(value);
                    break;
                }
            }

            let l = windows.len() - 1;

            let (mut dummy_cs, _, _) = create_test_artifacts();
            let cs = &mut dummy_cs;
            inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

            let mut chunks = vec![];
            for w in &windows {
                let c = UInt16::allocate(cs, Some(*w as u16))?;
                chunks.push(c);
            }

            println!("Using {} windows for window width {}", chunks.len(), width);

            let n = cs.n();

            let circuit = mul_fixed_point_by_variable_scalar::<_, _, _, 8>(
                cs,
                base,
                width,
                &rns_params,
                &chunks
            )?;

            let used = cs.n() - n;
            println!("Used {} gates for multiplication with window width {}", used, width);
            assert!(cs.is_satisfied());
        }

        Ok(())
    }

    #[test]
    fn test_naive_fixed_base_multiplication() -> Result<(), SynthesisError> {
        let rns_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let scalar_bits = 256;

        let (mut dummy_cs, _, _) = create_test_artifacts();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let p = AffinePoint::alloc(cs, Some(base), &rns_params)?;

        let mut rng = crate::testing::deterministic_rng();

        let random_point: PointAffine = rng.gen();

        let mut entries = vec![];
        for _ in 0..scalar_bits {
            let witness: bool = rng.gen();
            let bit = Boolean::alloc(cs, Some(witness))?;
            entries.push(bit);
        }

        let n = cs.n();

        let _ = p.mul_by_skewed_scalar_decomposition(
            cs,
            &entries,
            random_point
        )?;
        
        let used = cs.n() - n;
        println!("Used {} gates for naive multiplication", used);
        assert!(cs.is_satisfied());

        Ok(())
    }

    #[test]
    fn test_fixed_base_signed_multiplication() -> Result<(), SynthesisError> {
        let rns_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let scalar_bits = 256;

        let widths = vec![3, 4, 5, 6, 7, 8];
        for width in widths {
            let mask = (1<<(width-1)) - 1;
            let mut windows = vec![];
            let mut num_additions = scalar_bits / (width + 1);
            if scalar_bits % (width + 1) != 0 {
                num_additions += 1;
            }
            let mut rng = crate::testing::deterministic_rng();

            for _ in 0..num_additions {
                let flag: bool = rng.gen();
                let mut value = rng.gen::<usize>() & mask;
                // only odd powers
                if value & 1 != 1 {
                    value ^= 1;
                }
                windows.push((flag, value));
            }

            let (mut dummy_cs, _, _) = create_test_artifacts();
            let cs = &mut dummy_cs;
            inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

            let mut chunks = vec![];
            for (f, w) in &windows {
                let flag = Boolean::alloc(cs, Some(*f))?;
                let c = UInt16::allocate(cs, Some(*w as u16))?;
                chunks.push((flag, c));
            }

            println!("Using {} windows for window width {} for signed multiplication", chunks.len(), width);

            let n = cs.n();

            let circuit = signed_mul_fixed_point_by_variable_scalar::<_, _, _, 8>(
                cs,
                base,
                width,
                &rns_params,
                &chunks
            )?;

            let used = cs.n() - n;
            println!("Used {} gates for signed multiplication with window width {}", used, width);
            assert!(cs.is_satisfied());
        }

        Ok(())
    }

    #[test]
    fn test_variable_base_unsigned_table_based_multiplication() -> Result<(), SynthesisError> {
        let rns_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let scalar_bits = 256;

        let widths = vec![3, 4, 5, 6, 7, 8];
        for width in widths {
            let mask = (1<<width) - 1;
            let mut windows = vec![];
            let mut num_additions = scalar_bits / width;
            if scalar_bits % width != 0 {
                num_additions += 1;
            }
            let mut rng = crate::testing::deterministic_rng();

            for _ in 0..num_additions {
                let mut value = rng.gen::<usize>() & mask;
                // only odd powers
                windows.push(value);
            }

            let (mut dummy_cs, _, _) = create_test_artifacts();
            let cs = &mut dummy_cs;
            inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

            let mut chunks = vec![];
            for w in &windows {
                let c = UInt16::allocate(cs, Some(*w as u16))?;
                chunks.push(c);
            }

            let base = AffinePoint::alloc(cs, Some(base), &rns_params)?;
            println!("Using {} windows for window width {} for unsigned multiplication", chunks.len(), width);

            let n = cs.n();

            let circuit = mul_variable_point_by_variable_scalar::<_, _, _, 8>(
                cs,
                base,
                width,
                &rns_params,
                &chunks
            )?;

            let used = cs.n() - n;
            println!("Used {} gates for unsigned multiplication with window width {}", used, width);
            assert!(cs.is_satisfied());
        }

        Ok(())
    }

    #[test]
    fn test_variable_base_signed_multiplication() -> Result<(), SynthesisError> {
        let rns_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let scalar_bits = 256;

        let widths = vec![3, 4, 5, 6, 7, 8];
        for width in widths {
            let mask = (1<<(width-1)) - 1;
            let mut windows = vec![];
            let mut num_additions = scalar_bits / (width + 1);
            if scalar_bits % (width + 1) != 0 {
                num_additions += 1;
            }
            let mut rng = crate::testing::deterministic_rng();

            for _ in 0..num_additions {
                let flag: bool = rng.gen();
                let mut value = rng.gen::<usize>() & mask;
                // only odd powers
                if value & 1 != 1 {
                    value ^= 1;
                }
                windows.push((flag, value));
            }

            let (mut dummy_cs, _, _) = create_test_artifacts();
            let cs = &mut dummy_cs;
            inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

            let mut chunks = vec![];
            for (f, w) in &windows {
                let flag = Boolean::alloc(cs, Some(*f))?;
                let c = UInt16::allocate(cs, Some(*w as u16))?;
                chunks.push((flag, c));
            }

            let base = AffinePoint::alloc(cs, Some(base), &rns_params)?;
            println!("Using {} windows for window width {} for signed multiplication", chunks.len(), width);

            let n = cs.n();

            let circuit = signed_mul_variable_point_by_variable_scalar::<_, _, _, 8>(
                cs,
                base,
                width,
                &rns_params,
                &chunks
            )?;

            let used = cs.n() - n;
            println!("Used {} gates for signed multiplication with window width {}", used, width);
            assert!(cs.is_satisfied());
        }

        Ok(())
    }

    #[test]
    fn test_multiple_fixed_base_multiplications() -> Result<(), SynthesisError> {
        let rns_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let scalar_bits = 256;

        let mut num_points = vec![4, 8, 12, 16];

        // let widths = vec![3, 4, 5, 6, 7, 8];
        let widths = vec![6, 7, 8];
        for width in widths {
            for num_points in &num_points {
                let mut mul_table = MulTable::<_, _, 8>::new_for_fixed_point(base, width, &rns_params);
                let (mut dummy_cs, _, _) = create_test_artifacts();
                let cs = &mut dummy_cs;
                inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;
    
                let n = cs.n();

                for _ in 0..(*num_points) {
                    let mask = (1<<(width-1)) - 1;
                    let mut windows = vec![];
                    let mut num_additions = scalar_bits / width;
                    if scalar_bits % width != 0 {
                        num_additions += 1;
                    }
                    let mut rng = crate::testing::deterministic_rng();

                    for _ in 0..num_additions {
                        let mut value = rng.gen::<usize>() & mask;
                        windows.push(value);
                    }

                    let mut chunks = vec![];
                    for w in &windows {
                        let c = UInt16::allocate(cs, Some(*w as u16))?;
                        chunks.push(c);
                    }

                    let _ = mul_by_variable_scalar_with_shared_table::<_, _, _, 8>(
                        cs,
                        &rns_params,
                        &chunks,
                        &mut mul_table
                    )?;
                }

                mul_table.enforce_validity_optimized(cs)?;

                let used = cs.n() - n;
                let used = used / num_points;
                println!("Used {} gates per point for window multiplication with window width {} for {} points", used, width, num_points);

                assert!(cs.is_satisfied());
            }
        }

        Ok(())
    }

    #[test]
    fn test_multiple_fixed_base_signed_multiplications() -> Result<(), SynthesisError> {
        let rns_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let scalar_bits = 256;

        let mut num_points = vec![4, 8, 12, 16];

        // let widths = vec![3, 4, 5, 6, 7, 8];
        let widths = vec![6, 7, 8];
        for width in widths {
            for num_points in &num_points {
                let mut mul_table = MulTable::<_, _, 8>::new_signed_for_fixed_point(base, width, &rns_params);
                let (mut dummy_cs, _, _) = create_test_artifacts();
                let cs = &mut dummy_cs;
                inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;
    
                let n = cs.n();

                for _ in 0..(*num_points) {
                    let mask = (1<<(width-1)) - 1;
                    let mut windows = vec![];
                    let mut num_additions = scalar_bits / (width + 1);
                    if scalar_bits % (width + 1) != 0 {
                        num_additions += 1;
                    }
                    let mut rng = crate::testing::deterministic_rng();

                    for _ in 0..num_additions {
                        let flag: bool = rng.gen();
                        let mut value = rng.gen::<usize>() & mask;
                        // only odd powers
                        if value & 1 != 1 {
                            value ^= 1;
                        }
                        windows.push((flag, value));
                    }


                    let mut chunks = vec![];
                    for (f, w) in &windows {
                        let flag = Boolean::alloc(cs, Some(*f))?;
                        let c = UInt16::allocate(cs, Some(*w as u16))?;
                        chunks.push((flag, c));
                    }

                    let _ = signed_mul_by_variable_scalar_with_shared_table::<_, _, _, 8>(
                        cs,
                        &rns_params,
                        &chunks,
                        &mut mul_table
                    )?;
                }

                mul_table.enforce_validity_optimized(cs)?;

                let used = cs.n() - n;
                let used = used / num_points;
                println!("Used {} gates per point for signed multiplication with window width {} for {} points", used, width, num_points);

                assert!(cs.is_satisfied());
            }
        }

        Ok(())
    }

    #[test]
    fn test_validity_of_fixed_base_multiplication() -> Result<(), SynthesisError> {
        let base_params = RnsParameters::<E, Fq>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let scalar_params = RnsParameters::<E, FrSecp256>::new_for_field_with_strategy(
            80, 
            110, 
            4, 
            RangeConstraintInfo {
                minimal_multiple: 16,
                optimal_multiple: 16,
                multiples_per_gate: 1,
                linear_terms_used: 3,
                strategy: RangeConstraintStrategy::SingleTableInvocation,
            },
            true
        );

        let base = PointAffine::one();

        let mut rng = crate::testing::deterministic_rng();

        let (mut dummy_cs, _, _) = create_test_artifacts();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;
        let width = 8;
        let scalar: FrSecp256 = rng.gen();
        let scalar: FrSecp256 = {
            let value = 3u64;
            let mut repr = FrSecp256::zero().into_repr();
            repr.as_mut()[0] = value;
        
            FrSecp256::from_repr(repr).unwrap()
        };

        let naive_result = base.mul(scalar.into_repr()).into_affine();

        let scalar = FieldElement::new_allocated(cs, Some(scalar), &scalar_params)?;

        let (limbs, widths) = create_info(scalar);
        let scalar_decomposition = decompose(cs, &limbs, &widths, width, 256)?;

        let n = cs.n();

        let circuit_result = mul_fixed_point_by_variable_scalar::<_, _, _, 8>(
            cs,
            base,
            width,
            &base_params,
            &scalar_decomposition
        )?;

        assert_eq!(naive_result, circuit_result.get_value().unwrap());

        let used = cs.n() - n;
        println!("Used {} gates for multiplication with window width {}", used, width);
        assert!(cs.is_satisfied());

        Ok(())
    }
}   