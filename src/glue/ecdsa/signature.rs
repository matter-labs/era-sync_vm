use super::*;
use super::curve::*;

use franklin_crypto::plonk::circuit::curve::*;
use franklin_crypto::plonk::circuit::bigint::*;

pub struct ECDSASignature<'a, E: Engine, G: GenericCurveAffine> where G::Base: PrimeField + SqrtField {
    pub r: FieldElement<'a, E, G::Scalar>,
    pub s: FieldElement<'a, E, G::Scalar>,
}

impl<'a, E: Engine, G: GenericCurveAffine> ECDSASignature<'a, E, G> where G::Base: PrimeField + SqrtField {
    pub fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        scalar_params: &'a RnsParameters<E, G::Scalar>,
        witness: Option<ECDSARecoverableSignatureWitness<G>>,
    ) -> Result<Self, SynthesisError> {
        let r = witness.map(|el| el.r);
        let r = FieldElement::new_allocated(cs, r, scalar_params)?;

        let s = witness.map(|el| el.s);
        let s = FieldElement::new_allocated(cs, s, scalar_params)?;

        let new = Self {
            r,
            s
        };

        Ok(new)
    }
}

pub struct ECDSARecoverableSignatureExt<'a, E: Engine, G: GenericCurveAffine> where G::Base: PrimeField + SqrtField {
    r: AffinePoint<'a, E, G>,
    s: FieldElement<'a, E, G::Scalar>,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct ECDSARecoverableSignatureWitness<G: GenericCurveAffine> {
    pub r: G::Scalar,
    pub s: G::Scalar,
    pub v: bool,
}

impl<G: GenericCurveAffine> ECDSARecoverableSignatureWitness<G> {
    pub fn empty() -> Self {
        Self {
            r: G::Scalar::one(),
            s: G::Scalar::one(),
            v: false,
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct ECDSARecoverableSignatureWitnessExtended<G: GenericCurveAffine, const N: usize> {
    pub s: G::Scalar,
    pub r_point_candidates: [G; N],
}

pub fn transmute_representation<T: PrimeFieldRepr, U: PrimeFieldRepr>(repr: T) -> U {
    assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<U>());

    unsafe { std::mem::transmute_copy::<T, U>(&repr) }
}

impl<G: GenericCurveAffine, const N: usize> ECDSARecoverableSignatureWitnessExtended<G, N> where G::Base: PrimeField + SqrtField {
    pub fn from_signature_witness(witness: ECDSARecoverableSignatureWitness<G>) -> Self {
        assert!(N > 0);
        assert!(N <= 2);

        let r_repr = witness.r.into_repr();
        let group_order = G::Scalar::char();

        // let base_field_order = G::Base::char();

        // unsafe, but why not?
        assert_eq!(std::mem::size_of::<<G::Scalar as PrimeField>::Repr>(), std::mem::size_of::<<G::Base as PrimeField>::Repr>());

        let r_in_base_repr = transmute_representation::<_, <G::Base as PrimeField>::Repr>(r_repr);
        let group_order_in_base_repr = transmute_representation::<_, <G::Base as PrimeField>::Repr>(group_order);
        let mut r_point_candidates = [G::zero(); N];
        let mut tmp = r_in_base_repr;
        for i in 0..N {
            if let Ok(x) = G::Base::from_repr(tmp) {
                // recover Y
                let mut x2 = x;
                x2.square();
                let mut x3 = x2;
                x3.mul_assign(&x);

                let mut rhs = x;
                rhs.mul_assign(&G::a_coeff());
                rhs.add_assign(&G::b_coeff());
                rhs.add_assign(&x3);

                if let Some(y) = rhs.sqrt() {
                    let mut y_negated = y;
                    y_negated.negate();

                    let y_bit = y.into_repr().as_ref()[0] & 1 > 0;
                    let y_chosen = if y_bit && witness.v {
                        y
                    } else {
                        y_negated
                    };

                    r_point_candidates[i] = G::from_xy_unchecked(x, y_chosen);
                }
            }

            tmp.add_nocarry(&group_order_in_base_repr);
        }

        Self {
            s: witness.s,
            r_point_candidates,
        }
    }
}

impl<'a, E: Engine, G: GenericCurveAffine> ECDSARecoverableSignatureExt<'a, E, G> where G::Base: PrimeField + SqrtField {
    pub fn allocate_from_witness<CS: ConstraintSystem<E>, const N: usize>(
        cs: &mut CS,
        base_params: &'a RnsParameters<E, G::Base>,
        scalar_params: &'a RnsParameters<E, G::Scalar>,
        witness: Option<ECDSARecoverableSignatureWitnessExtended<G, N>>,
        candidate_idx: usize
    ) -> Result<Self, SynthesisError> {
        assert!(N > 0);
        assert!(N <= 2);
        assert!(candidate_idx < N);
        // we will need to cast perform modular reduction from one field to another,
        // so let's make sure that we've made our life easier
        assert_eq!(base_params.num_binary_limbs, scalar_params.num_binary_limbs);
        assert_eq!(base_params.num_limbs_for_in_field_representation, scalar_params.num_limbs_for_in_field_representation);
        assert_eq!(base_params.binary_limbs_bit_widths, scalar_params.binary_limbs_bit_widths);
        assert_eq!(base_params.binary_limbs_max_values, scalar_params.binary_limbs_max_values);
        assert_eq!(base_params.prefer_single_limb_allocation, scalar_params.prefer_single_limb_allocation);
        assert_eq!(base_params.prefer_single_limb_carry_propagation, scalar_params.prefer_single_limb_carry_propagation);

        assert_eq!(base_params.range_check_info, scalar_params.range_check_info);

        let r = witness.map(|el| el.r_point_candidates[candidate_idx]);
        let r = AffinePoint::alloc(cs, r, base_params)?;

        let s = witness.map(|el| el.s);
        let s = FieldElement::new_allocated(cs, s, scalar_params)?;

        let new = Self {
            r,
            s,
        };

        Ok(new)
    }

    pub fn recover_key<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
        message_digest: FieldElement<'a, E, G::Scalar>,
        // here we will also have precomputed window table for multiplication by generator
    ) -> Result<AffinePoint<'a, E, G>, SynthesisError> {
        // first we need to make r from X coordinate of the point in the base field to the scalar field

        // quick and dirty trick because we have same representation parameters everywhere
        let FieldElement{
            binary_limbs,
            base_field_limb,
            value,
            ..
        } = self.r.x;

        let value = value.map(|el| {
            let repr = el.into_repr();
            let repr = transmute_representation::<_, <G::Scalar as PrimeField>::Repr>(repr);

            if let Ok(value) = G::Scalar::from_repr(repr) {
                value
            } else {
                let mut repr = repr;
                repr.sub_noborrow(&G::Scalar::char());

                G::Scalar::from_repr(repr).expect("must fit into the field")
            }
        });

        let r_in_scalar_field = FieldElement {
            binary_limbs,
            base_field_limb,
            value,
            representation_params: self.s.representation_params
        };

        let one = FieldElement::new_constant(G::Scalar::one(), self.s.representation_params);

        let (r_inv, _) = one.div(cs, r_in_scalar_field)?;

        let (mul_by_base, (r_inv, _)) = r_inv.mul(cs, message_digest)?;
        let (mul_by_r, _) = r_inv.mul(cs, self.s)?;

        // perform fixed base multiplication

        // perform varirable base multiplication

        todo!()
    }
}

/// Caller must assert that coordiantes are normalized if correct behavior is required
pub fn public_key_into_bytes<'a, E: Engine, CS: ConstraintSystem<E>, G: GenericCurveAffine, const N: usize> (
    cs: &mut CS,
    pk_x: FieldElement<'a, E, G::Base>,
    pk_y: FieldElement<'a, E, G::Base>,
) -> Result<[Byte<E>; N], SynthesisError> where G::Base: PrimeField {
    assert!(N % 2 == 0);
    let params = pk_x.representation_params;
    // assert_eq!(pk_x.representation_params, pk_y.representation_params);

    for w in  pk_x.representation_params.binary_limbs_bit_widths.iter() {
        if w % 8 != 0 {
            unimplemented!();
        }
    }

    assert!(<G::Base as PrimeField>::NUM_BITS as usize <= N * 4); 

    let mut result = [Byte::<E>::empty(); N];
    let (x_bytes, y_bytes) = result.split_at_mut(N/2);

    let mut x_bytes_candidate_be = vec![];
    for (l, w) in pk_x.binary_limbs.into_iter().zip(params.binary_limbs_bit_widths.iter()) {
        let limb_bytes = num_into_bytes_le(cs, l.term.into_num(), *w)?;
        x_bytes_candidate_be.extend(limb_bytes);
    }

    let mut y_bytes_candidate_be = vec![];
    for (l, w) in pk_y.binary_limbs.into_iter().zip(params.binary_limbs_bit_widths.iter()) {
        let limb_bytes = num_into_bytes_le(cs, l.term.into_num(), *w)?;
        y_bytes_candidate_be.extend(limb_bytes);
    }

    assert!(x_bytes_candidate_be.len() <= x_bytes.len());
    assert!(y_bytes_candidate_be.len() <= y_bytes.len());
    assert_eq!(x_bytes_candidate_be.len(), y_bytes_candidate_be.len());

    x_bytes_candidate_be.reverse();
    y_bytes_candidate_be.reverse();

    // now just emplace

    let skip = x_bytes.len() - x_bytes_candidate_be.len();
    x_bytes[skip..].copy_from_slice(&x_bytes_candidate_be);
    y_bytes[skip..].copy_from_slice(&y_bytes_candidate_be);

    drop(x_bytes);
    drop(y_bytes);

    Ok(result)
}

// pub fn num_into_bytes_le<E: Engine, CS: ConstraintSystem<E>>(
//     cs: &mut CS,
//     limb: Num<E>,
//     width: usize
// ) -> Result<Vec<Byte<E>>, SynthesisError> {
//     assert!(width % 8 == 0);

//     let num_bytes = width / 8;
//     let result = match &limb {
//         Num::Variable(ref var) => {
//             let mut minus_one = E::Fr::one();
//             minus_one.negate();
//             let factor = E::Fr::from_str("256").unwrap();
//             let mut coeff = E::Fr::one();
//             let mut result = Vec::with_capacity(num_bytes);
//             let mut lc = LinearCombination::zero();
//             lc.add_assign_number_with_coeff(&limb, minus_one);
//             let witness = split_some_into_slices(var.get_value(), 8, num_bytes);
//             for w in witness.into_iter() {
//                 let allocated = AllocatedNum::alloc(
//                     cs,
//                     || {
//                         Ok(*w.get()?)
//                     }
//                 )?;
//                 let num = Num::Variable(allocated);
//                 let byte = Byte::from_num(cs, num.clone())?;
//                 result.push(byte);

//                 lc.add_assign_number_with_coeff(&num, coeff);
//                 coeff.mul_assign(&factor);
//             }

//             lc.enforce_zero(cs)?;

//             result
//         },
//         Num::Constant(constant) => {
//             let mut result = Vec::with_capacity(num_bytes);
//             let witness = split_into_slices(constant, 8, num_bytes);
//             for w in witness.into_iter() {
//                 let num = Num::Constant(w);
//                 let byte = Byte::from_num(cs, num)?;
//                 result.push(byte);
//             }

//             result
//         }
//     };
    
//     Ok(result)
// }

// pub fn num_into_bytes_be<E: Engine, CS: ConstraintSystem<E>>(
//     cs: &mut CS,
//     limb: Num<E>,
//     width: usize
// ) -> Result<Vec<Byte<E>>, SynthesisError> {
//     let mut encoding = num_into_bytes_le(cs, limb, width)?;
//     encoding.reverse();

//     Ok(encoding)
// }