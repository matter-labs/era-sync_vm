use super::*;
use crate::vm::primitives::UInt16;
use num_bigint::*;
use num_integer::*;
use num_traits::ToPrimitive;

pub fn decompose<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    scalar_limbs: &[Num<E>],
    limb_widths: &[usize],
    window_size: usize,
    scalar_bit_limit: usize
) -> Result<Vec<UInt16<E>>, SynthesisError> {
    // create some witness
    let witness = witness(
        scalar_limbs,
        limb_widths,
        window_size,
        scalar_bit_limit
    )?;

    // now it's a little more involved, so first a simple case

    for w in limb_widths.iter() {
        if w % window_size != 0 {
            unimplemented!("decomposition for non-matching width is not yet implemented: limb width = {}, window size = {}", w, window_size);
        }
    }
    let mut it = witness.into_iter();
    let shifts = compute_shifts::<E::Fr>();

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut result = vec![];

    for (l, w) in scalar_limbs.iter().zip(limb_widths.iter()) {
        let take_by = w / window_size;
        let mut shift = 0;
        let mut lc = LinearCombination::zero();
        for _ in 0..take_by {
            let wit = (&mut it).next().expect("is some").map(|el| u16_to_fe(el));
            let wit = Num::alloc(cs, wit)?;
            constraint_bit_length(cs, &wit, window_size)?;
            lc.add_assign_number_with_coeff(&wit, shifts[shift]);

            shift += window_size;
            let wit = UInt16::from_num_unchecked(wit);
            result.push(wit);
        }
        lc.add_assign_number_with_coeff(l, minus_one);
        lc.enforce_zero(cs)?;
    }

    // we need most significant first
    result.reverse();

    Ok(result)
}

fn witness<E: Engine>(
    scalar_limbs: &[Num<E>],
    limb_widths: &[usize],
    window_size: usize,
    scalar_bit_limit: usize
) -> Result<Vec<Option<u16>>, SynthesisError> {
    let mut num_windows = scalar_bit_limit / window_size;
    if scalar_bit_limit % window_size != 0 {
        num_windows += 1;
    }

    assert!(window_size <= 16);
    let mut scalar = BigUint::from(0u64);
    let mut shift = 0;
    for (l, w) in scalar_limbs.iter().zip(limb_widths.iter()) {
        let chunk = if let Some(value) = l.get_value() {
            let as_bigint = fe_to_biguint(&value);

            as_bigint
        } else {
            return Ok(vec![None; num_windows])
        };

        scalar += chunk << shift;
        shift += w;
    }

    assert!(scalar.bits() <= scalar_bit_limit as u64);

    // perform a decomposition
    let mut result = vec![];

    let mask = ((1 << window_size) - 1) as u64;

    let lowest_word_divisor = BigUint::from(1u64) << 64;

    for _ in 0..num_windows {
        let lowest: BigUint = &scalar % & lowest_word_divisor;
        let lowest = lowest.to_u64().unwrap();
        let masked_bits = lowest & mask;
        result.push(Some(masked_bits as u16));
        scalar -= BigUint::from(masked_bits);
        if let Some(trailing) = scalar.trailing_zeros() {
            assert!(trailing >= window_size as u64, "have {} trailing zeroes, expected at least {}", trailing, window_size);
        }
        scalar >>= window_size;
    }

    assert_eq!(result.len(), num_windows);
    assert_eq!(scalar, BigUint::from(0u64));

    Ok(result)
}

#[track_caller]
pub fn signed_decompose<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    scalar_limbs: &[Num<E>],
    limb_widths: &[usize],
    window_size: usize,
    scalar_bit_limit: usize
) -> Result<Vec<(Boolean, UInt16<E>)>, SynthesisError> {
    // create some witness
    let mut witness = signed_witness(
        scalar_limbs,
        limb_widths,
        window_size,
        scalar_bit_limit
    )?;

    let base = (E::Fr::CAPACITY as usize / window_size) * window_size;

    let mut sets = vec![];

    let mut limit = base;
    let mut set = vec![];
    for (l, w) in scalar_limbs.iter().zip(limb_widths.iter()) {
        if *w <= limit {
            limit -= w;
            set.push((*l, *w));
        } else {
            sets.push(set);
            set = vec![];
            limit = base;
            limit -= w;
            set.push((*l, *w));
        }
    }
    if !set.is_empty() {
        sets.push(set);
    }

    let shifts = compute_shifts::<E::Fr>();

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut minus_two = minus_one;
    minus_two.double();

    let mut result = vec![];

    let mut carry = None;
    let num_sets = sets.len();

    for (idx, set) in sets.into_iter().enumerate() {
        let mut total_length = 0;
        for (_, w) in set.iter() {
            total_length += w;
        }
        let (take_by, carry_width) = if idx == num_sets - 1 {
            (witness.len(), 0)
        } else {
            let mut take_by = total_length / window_size;
            let mut carry_width = total_length - take_by * window_size;
            if carry_width == 0 {
                // we have signed decomposition, so use one less chunk to avoid underflow
                // or overflow
                take_by -= 1;
                carry_width += window_size;
            }

            (take_by, carry_width)
        };

        let mut shift = 0;
        let mut lc = LinearCombination::zero();
        // if we had some leftover form the previous round then add it here
        if let Some((carry_width, carry)) = carry.take() {
            lc.add_assign_number_with_coeff(&carry, shifts[0]);
            shift += carry_width;
        }
        for (l, w) in set.into_iter() {
            lc.add_assign_number_with_coeff(&l, shifts[shift]);
            shift += w;
        }

        shift = 0;
        // here we have to do more work
        for witness in witness.drain(0..take_by).into_iter() {
            let sign_boolean = witness.map(|el| el.0);
            let sign_boolean = Boolean::alloc(cs, sign_boolean)?;

            let absolute_value = witness.map(|el| u16_to_fe(el.1));
            let absolute_value = Num::alloc(cs, absolute_value)?;
            constraint_bit_length(cs, &absolute_value, window_size)?;
            let absolute_value = UInt16::from_num_unchecked(absolute_value);

            use franklin_crypto::plonk::circuit::simple_term::Term;
            // we need to map false into 1, true into -1
            // so we make it 1 - 2 * bool
            let mut sign_term = Term::from_boolean(&sign_boolean);
            sign_term.scale(&minus_two);
            sign_term.add_constant(&E::Fr::one());

            // signed digit that is left shifted as much as necessary
            let mut signed_digit_term = Term::from_num(absolute_value.inner);
            signed_digit_term.scale(&shifts[shift]);
            let mut signed_digit_term = signed_digit_term.mul(cs, &sign_term)?;
            // negate and add into lc
            signed_digit_term.negate();

            lc.add_assign_term(&signed_digit_term);
            shift += window_size;

            result.push((sign_boolean, absolute_value));
        }

        if idx == num_sets - 1 {
            assert!(witness.is_empty());
        }

        // now we shift everything to the right and constraint bit length of the leftover
        if carry_width == 0 {
            lc.enforce_zero(cs)?;
        } else {
            shift = total_length - carry_width;
            let shift = shifts[shift].inverse().unwrap();
            lc.scale(&shift);
            let next_carry = lc.into_num(cs)?;
            constraint_bit_length(cs, &next_carry, carry_width)?;
            carry = Some((carry_width, next_carry));
        }
    }

    // we need most significant first
    result.reverse();

    Ok(result)
}

fn signed_witness<E: Engine>(
    scalar_limbs: &[Num<E>],
    limb_widths: &[usize],
    window_size: usize,
    scalar_bit_limit: usize
) -> Result<Vec<Option<(bool, u16)>>, SynthesisError> {
    let mut num_windows = scalar_bit_limit / window_size;
    if scalar_bit_limit % window_size != 0 {
        num_windows += 1;
    } else if scalar_bit_limit % window_size == 0 {
        // we need a carry bit
        num_windows += 1;
    }

    assert!(window_size <= 16);
    let mut scalar = BigUint::from(0u64);
    let mut shift = 0;
    for (l, w) in scalar_limbs.iter().zip(limb_widths.iter()) {
        let chunk = if let Some(value) = l.get_value() {
            let as_bigint = fe_to_biguint(&value);

            as_bigint
        } else {
            return Ok(vec![None; num_windows])
        };

        scalar += chunk << shift;
        shift += w;
    }

    assert!(scalar.bits() <= scalar_bit_limit as u64, "trying to decompose a scalar of bit width up to {} bits, got a value that is {} bits long", scalar_bit_limit, scalar.bits());

    // perform a decomposition
    let mut result = vec![];

    let base = (1 << window_size) as u64;
    let mask = base - 1;
    let midpoint = (1 << (window_size - 1)) as u64;

    let lowest_word_divisor = BigUint::from(1u64) << 64;

    for i in 0..num_windows {
        let lowest: BigUint = &scalar % & lowest_word_divisor;
        let lowest = lowest.to_u64().unwrap();
        let masked_bits = lowest & mask;
        if i == num_windows - 1 {
            assert!(masked_bits < midpoint)
        }
        if masked_bits >= midpoint {
            let absolute_value = base - masked_bits;
            result.push(Some((true, absolute_value as u16)));
            scalar -= BigUint::from(masked_bits);
            scalar += BigUint::from(base);
        } else {
            result.push(Some((false, masked_bits as u16)));
            scalar -= BigUint::from(masked_bits);
        }
        if let Some(trailing) = scalar.trailing_zeros() {
            assert!(trailing >= window_size as u64, "have {} trailing zeroes, expected at least {}", trailing, window_size);
        }
        scalar >>= window_size;
    }

    assert_eq!(result.len(), num_windows);
    assert_eq!(scalar, BigUint::from(0u64));

    Ok(result)
}

#[cfg(test)]
mod test {
    use crate::testing::*;
    use super::*;

    #[test]
    fn test_decomposition() -> Result<(), SynthesisError> {
        let mut rng = deterministic_rng();
        let (mut dummy_cs, _, _) = create_test_artifacts();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let widths = vec![64; 4];
        let limit = 256;
        let window_size = 5;
        let mut limbs = vec![];
        for _ in 0..4 {
            let w: u64 = rng.gen();
            let w = Num::alloc(cs, Some(u64_to_fe(w)))?;
            limbs.push(w);
        }

        let decomposition = witness(&limbs, &widths, window_size, 256)?;

        Ok(())
    }

    #[test]
    fn test_signed_decomposition() -> Result<(), SynthesisError> {
        let mut rng = deterministic_rng();
        let (mut dummy_cs, _, _) = create_test_artifacts();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let widths = vec![64, 64, 64, 64];
        let limit = 256;
        let window_size = 5;
        let mut limbs = vec![];
        for _ in 0..4 {
            let w: u64 = rng.gen();
            let w = Num::alloc(cs, Some(u64_to_fe(w)))?;
            limbs.push(w);
        }

        let _ = signed_decompose(
            cs,
            &limbs,
            &widths,
            window_size,
            256,
        )?;

        assert!(cs.is_satisfied());

        Ok(())
    }
}