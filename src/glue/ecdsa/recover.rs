use super::*;
use super::curve::curve::PointAffine;
use super::signature::*;
use super::curve::mul_routine::*;
use super::curve::mul_table::MulTable;
use super::curve::decomposition::*;

use franklin_crypto::plonk::circuit::curve::*;
use franklin_crypto::plonk::circuit::bigint::*;

use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::*;

pub struct ECRecoverContext<'a, E: Engine, G: GenericCurveAffine, const N: usize> where G::Base: PrimeField {
    window_size: usize,
    shared_table: Option<MulTable<'a, E, G, N>>,
    scalar_params: &'a RnsParameters<E, G::Scalar>,
    base_params: &'a RnsParameters<E, G::Base>,
    keccak_gadget: Option<Keccak256Gadget<E>>,
}

impl<'a, E: Engine, G: GenericCurveAffine, const N: usize> Drop for ECRecoverContext<'a, E, G, N> where G::Base: PrimeField {
    #[track_caller]
    fn drop(&mut self) {
        assert!(self.shared_table.is_none(), "must have called an `enforce` function before dropping");
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, const N: usize> ECRecoverContext<'a, E, G, N> where G::Base: PrimeField {
    pub fn new(
        window_size: usize,
        scalar_params: &'a RnsParameters<E, G::Scalar>,
        base_params: &'a RnsParameters<E, G::Base>
    ) -> Self {
        // we will need to cast perform modular reduction from one field to another,
        // so let's make sure that we've made our life easier
        assert_eq!(base_params.num_binary_limbs, scalar_params.num_binary_limbs);
        assert_eq!(base_params.num_limbs_for_in_field_representation, scalar_params.num_limbs_for_in_field_representation);
        assert_eq!(base_params.binary_limbs_bit_widths, scalar_params.binary_limbs_bit_widths);
        assert_eq!(base_params.binary_limbs_max_values, scalar_params.binary_limbs_max_values);
        assert_eq!(base_params.prefer_single_limb_allocation, scalar_params.prefer_single_limb_allocation);
        assert_eq!(base_params.prefer_single_limb_carry_propagation, scalar_params.prefer_single_limb_carry_propagation);

        assert_eq!(base_params.range_check_info, scalar_params.range_check_info);

        let generator = G::one();
        let shared_table = MulTable::<E, G, N>::new_for_fixed_point(generator, window_size, base_params);

        Self {
            window_size,
            shared_table: Some(shared_table),
            scalar_params,
            base_params,
            keccak_gadget: None,
        }
    }

    pub fn new_for_signed_multiplications(
        window_size: usize,
        scalar_params: &'a RnsParameters<E, G::Scalar>,
        base_params: &'a RnsParameters<E, G::Base>
    ) -> Self {
        // we will need to cast perform modular reduction from one field to another,
        // so let's make sure that we've made our life easier
        assert_eq!(base_params.num_binary_limbs, scalar_params.num_binary_limbs);
        assert_eq!(base_params.num_limbs_for_in_field_representation, scalar_params.num_limbs_for_in_field_representation);
        assert_eq!(base_params.binary_limbs_bit_widths, scalar_params.binary_limbs_bit_widths);
        assert_eq!(base_params.binary_limbs_max_values, scalar_params.binary_limbs_max_values);
        assert_eq!(base_params.prefer_single_limb_allocation, scalar_params.prefer_single_limb_allocation);
        assert_eq!(base_params.prefer_single_limb_carry_propagation, scalar_params.prefer_single_limb_carry_propagation);

        assert_eq!(base_params.range_check_info, scalar_params.range_check_info);

        let generator = G::one();
        let shared_table = MulTable::<E, G, N>::new_signed_for_fixed_point(generator, window_size, base_params);

        Self {
            window_size,
            shared_table: Some(shared_table),
            scalar_params,
            base_params,
            keccak_gadget: None,
        }
    }

    pub fn enforce<CS: ConstraintSystem<E>>(mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        let table = self.shared_table.take().expect("is some");

        table.enforce_validity_optimized(cs)
    }

    pub fn recover<CS: ConstraintSystem<E>>(
        &mut self,
        _cs: &mut CS,
        _witness: &ECDSARecoverableSignatureExt<'a, E, PointAffine>
    ) -> Result<AffinePoint<'a, E, PointAffine>, SynthesisError> {
        todo!();
    }

    pub fn verify_for_public_key<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        signature: ECDSASignature<'a, E, G>,
        public_key: AffinePoint<'a, E, G>,
        message_digest: FieldElement<'a, E, G::Scalar>,
        variable_point_table_width: usize,
    ) -> Result<Boolean, SynthesisError> {
        let one = FieldElement::new_constant(G::Scalar::one(), self.scalar_params);
        let ECDSASignature {r, s} = signature;
        let (s_inv, _s) = one.div(cs, s)?;
        let original_r_copy = r.clone();
        let (mul_by_generator, (s_inv, _)) = s_inv.mul(cs, message_digest)?;
        let (mul_by_public_key, _) = s_inv.mul(cs, r)?;

        let random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log_generic::<G::Projective>(b"ECVERIFY", 1)[0];
        let random_point = AffinePoint::constant(random_point, self.base_params);

        let mul_by_generator = mul_by_generator.enforce_is_normalized(cs)?;
        let mul_by_public_key = mul_by_public_key.enforce_is_normalized(cs)?;

        let scalar_bits = G::Scalar::NUM_BITS as usize;

        // let mut variable_base_table = MulTable::<E, G, N>::new_for_variable_point(cs, public_key, variable_point_table_width, self.base_params)?;

        // let (limbs, widths) = create_info(mul_by_generator);
        // let mul_by_generator_decomposition = decompose(cs, &limbs, &widths, self.window_size, scalar_bits)?;

        // let (limbs, widths) = create_info(mul_by_public_key);
        // let mul_by_public_key_decomposition = decompose(cs, &limbs, &widths, variable_point_table_width, scalar_bits)?;
        
        // let gen_mul_result = mul_by_variable_scalar_with_shared_table(
        //     cs,
        //     self.base_params,
        //     &mul_by_generator_decomposition,
        //     self.shared_table.as_mut().expect("is some")
        // )?;

        // let public_key_mul_result = mul_by_variable_scalar_with_shared_table(
        //     cs,
        //     self.base_params,
        //     &mul_by_public_key_decomposition,
        //     &mut variable_base_table
        // )?;

        // variable_base_table.enforce_validity_optimized(cs)?;

        let (limbs, widths) = create_info(mul_by_generator);
        let mul_by_generator_decomposition = signed_decompose(cs, &limbs, &widths, self.window_size, scalar_bits)?;

        let (limbs, widths) = create_info(mul_by_public_key);
        let mul_by_public_key_decomposition = signed_decompose(cs, &limbs, &widths, variable_point_table_width, scalar_bits)?;
        
        let gen_mul_result = signed_mul_by_variable_scalar_with_shared_table(
            cs,
            self.base_params,
            &mul_by_generator_decomposition,
            self.shared_table.as_mut().expect("is some")
        )?;

        let public_key_mul_result = signed_mul_variable_point_by_variable_scalar::<E, _, G, N>(
            cs,
            public_key,
            variable_point_table_width,
            self.base_params,
            &mul_by_public_key_decomposition,
        )?;

        let (lhs, _) = random_point.clone().add_unequal(cs, gen_mul_result.clone())?;
        let (lhs, _) = lhs.clone().add_unequal(cs, public_key_mul_result)?;

        let (is_zero, (lhs, _)) = AffinePoint::equals(cs, lhs, random_point.clone())?;
        // just take anything literally
        let (lhs, _) = AffinePoint::select(cs, &is_zero, gen_mul_result, lhs)?;
        let (rhs, _) = lhs.sub_unequal(cs, random_point)?;

        let x = rhs.x.enforce_is_normalized(cs)?;
        // cast to scalar field

        // quick and dirty trick because we have same representation parameters everywhere
        let FieldElement{
            binary_limbs,
            base_field_limb,
            value,
            ..
        } = x;

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
            representation_params: self.scalar_params
        };

        let r_in_scalar_field = r_in_scalar_field.enforce_is_normalized(cs)?;

        let (valid, _) = FieldElement::equals(cs, r_in_scalar_field, original_r_copy)?;

        let valid = Boolean::and(cs, &valid, &is_zero.not())?;

        Ok(valid)
    }

    pub fn verify_for_ethereum_address<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        signature: ECDSASignature<'a, E, G>,
        public_key_witness: Option<G>,
        message_digest: FieldElement<'a, E, G::Scalar>,
        variable_point_table_width: usize,
        ethereum_address: &[Byte<E>; 20]
    ) -> Result<Boolean, SynthesisError> {
        use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::*;
        let pk = AffinePoint::alloc(cs, public_key_witness, self.base_params)?;
        let pk_bytes = public_key_into_bytes::<_, _, G, 64>(cs, pk.x.clone(), pk.y.clone())?;
        let reused_table_name = franklin_crypto::plonk::circuit::tables::RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME;
        
        let digest_size_u64_words = 4;
        let keccak_gadget = if let Some(gadget) = self.keccak_gadget.as_ref() {
            gadget
        } else {
            let keccak_gadget = Keccak256Gadget::new(
                cs, 
                None, 
                None, 
                None, 
                Some(digest_size_u64_words), 
                true, 
                &reused_table_name
            )?;
            self.keccak_gadget = Some(keccak_gadget);

            self.keccak_gadget.as_ref().unwrap()
        };
        
        let pk_hash_u64_words = keccak_gadget.digest_from_bytes(cs, &pk_bytes[..])?;
        // now convert
        let mut pk_hash_bytes = vec![];
        for word in pk_hash_u64_words.into_iter() {
            let bytes = crate::utils::num_into_bytes_le(cs, word, 64)?;
            pk_hash_bytes.extend(bytes);
        }

        assert_eq!(pk_hash_bytes.len(), 32);

        let address_is_correct = compare_bytes(cs, &ethereum_address[..], &pk_hash_bytes[12..])?;
        let signature_is_correct = self.verify_for_public_key(
            cs,
            signature,
            pk,
            message_digest,
            variable_point_table_width
        )?;

        let correct = Boolean::and(cs, &address_is_correct, &signature_is_correct)?;

        Ok(correct)
    }
}

pub fn compare_bytes<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, a: &[Byte<E>], b: &[Byte<E>]) -> Result<Boolean, SynthesisError> {
    assert_eq!(a.len(), b.len());
    let mut tmp_bools = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let tmp = Num::equals(cs, &a.inner, &b.inner)?;
        tmp_bools.push(tmp);
    }

    let eq = smart_and(cs, &tmp_bools)?;

    Ok(eq)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::testing::*;

    use super::super::curve::fq::Fq as Secp256Fq;
    use super::super::curve::fr::Fr as Secp256Fr;
    use super::super::curve::curve::*;

    type E = Bn256;

    fn simulate_signature()-> (Secp256Fr, Secp256Fr, PointAffine, Secp256Fr){
        let mut rng = deterministic_rng();
        let sk: Secp256Fr = rng.gen();

        simulate_signature_for_sk(sk)
    }

    fn simulate_signature_for_sk(sk: Secp256Fr) -> (Secp256Fr, Secp256Fr, PointAffine, Secp256Fr) {
        let mut rng = deterministic_rng();
        let pk = PointAffine::one().mul(sk.into_repr()).into_affine();
        let digest: Secp256Fr = rng.gen();
        let k: Secp256Fr = rng.gen();
        let r_point = PointAffine::one().mul(k.into_repr()).into_affine();
        let r_x = r_point.into_xy_unchecked().0;
        let r = transmute_representation::<_, <Secp256Fr as PrimeField>::Repr>(r_x.into_repr());
        let r = Secp256Fr::from_repr(r).unwrap();
        let k_inv = k.inverse().unwrap();
        let mut s = r;
        s.mul_assign(&sk);
        s.add_assign(&digest);
        s.mul_assign(&k_inv);

        {
            let s_inv = s.inverse().unwrap();
            let mut mul_by_generator = s_inv;
            mul_by_generator.mul_assign(&digest);

            let mut mul_by_public_key = s_inv;
            mul_by_public_key.mul_assign(&r);

            let res_1 = PointAffine::one().mul(mul_by_generator.into_repr());
            let res_2 = pk.mul(mul_by_public_key.into_repr());

            let mut tmp = res_1;
            tmp.add_assign(&res_2);

            let tmp = tmp.into_affine();

            let x = tmp.into_xy_unchecked().0;
            let r_recovered = transmute_representation::<_, <Secp256Fr as PrimeField>::Repr>(x.into_repr());
            let r_recovered = Secp256Fr::from_repr(r_recovered).unwrap();

            assert_eq!(r_recovered, r);
        }

        (r, s, pk, digest)
    }

    #[test]
    fn test_signature_verification() -> Result<(), SynthesisError> {
        let (mut dummy_cs, _, _) = create_test_artifacts();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let base_params = RnsParameters::<E, Secp256Fq>::new_for_field_with_strategy(
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

        let scalar_params = RnsParameters::<E, Secp256Fr>::new_for_field_with_strategy(
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

        // let mut ctx = ECRecoverContext::<_, _, 8>::new(8, &scalar_params, &base_params);
        let mut ctx = ECRecoverContext::<_, _, 8>::new_for_signed_multiplications(8, &scalar_params, &base_params);

        // let (r, s, pk, digest) = simulate_signature();

        let mut sk = Secp256Fr::one();
        sk.negate();
        let (r, s, pk, digest) = simulate_signature_for_sk(sk);

        let witness = ECDSARecoverableSignatureWitness {
            r,
            s,
            v: false
        };

        let n = cs.n();

        let signature = ECDSASignature::allocate_from_witness(cs, &scalar_params, Some(witness))?;
        let pk = AffinePoint::alloc(cs, Some(pk), &base_params)?;
        let digest = FieldElement::new_allocated(cs, Some(digest), &scalar_params)?;

        let is_valid = ctx.verify_for_public_key(
            cs, 
            signature, 
            pk, 
            digest, 
            4
        )?;

        ctx.enforce(cs)?;

        let used = cs.n() - n;
        println!("Used {} gates for single signature verification", used);

        assert!(is_valid.get_value().unwrap());
        assert!(cs.is_satisfied());

        Ok(())
    }

    #[test]
    fn test_signature_for_address_verification() -> Result<(), SynthesisError> {
        let (mut dummy_cs, _, _) = create_test_artifacts();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let base_params = RnsParameters::<E, Secp256Fq>::new_for_field_with_strategy(
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

        let scalar_params = RnsParameters::<E, Secp256Fr>::new_for_field_with_strategy(
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

        // let mut ctx = ECRecoverContext::<_, _, 8>::new(8, &scalar_params, &base_params);
        let mut ctx = ECRecoverContext::<_, _, 8>::new_for_signed_multiplications(8, &scalar_params, &base_params);

        let sk = crate::ff::from_hex::<Secp256Fr>("b5b1870957d373ef0eeffecc6e4812c0fd08f554b37b233526acc331bf1544f7").unwrap();
        let eth_address = hex::decode("12890d2cce102216644c59dae5baed380d84830c").unwrap();
        let (r, s, pk, digest) = simulate_signature_for_sk(sk);

        let witness = ECDSARecoverableSignatureWitness {
            r,
            s,
            v: false
        };

        let n = cs.n();

        let signature = ECDSASignature::allocate_from_witness(cs, &scalar_params, Some(witness))?;
        let digest = FieldElement::new_allocated(cs, Some(digest), &scalar_params)?;

        let mut address = [Byte::<E>::empty(); 20];
        for (i, b) in eth_address.into_iter().enumerate() {
            let b = Byte::constant(b);
            address[i] = b;
        }

        let is_valid = ctx.verify_for_ethereum_address(
            cs, 
            signature, 
            Some(pk), 
            digest, 
            4,
            &address
        )?;
        dbg!(is_valid.get_value());

        ctx.enforce(cs)?;

        let used = cs.n() - n;
        println!("Used {} gates for single signature for address verification", used);

        assert!(is_valid.get_value().unwrap());
        assert!(cs.is_satisfied());

        Ok(())
    }

    #[test]
    fn test_multiple_signature_verifications_for_address() -> Result<(), SynthesisError> {
        let (mut dummy_cs, _, _) = create_test_artifacts();
        let cs = &mut dummy_cs;
        inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

        let base_params = RnsParameters::<E, Secp256Fq>::new_for_field_with_strategy(
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

        let scalar_params = RnsParameters::<E, Secp256Fr>::new_for_field_with_strategy(
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

        let num_items = 16;

        let mut ctx = ECRecoverContext::<_, _, 8>::new_for_signed_multiplications(8, &scalar_params, &base_params);
        let n = cs.n();

        for _ in 0..num_items {
            let sk = crate::ff::from_hex::<Secp256Fr>("b5b1870957d373ef0eeffecc6e4812c0fd08f554b37b233526acc331bf1544f7").unwrap();
            let eth_address = hex::decode("12890d2cce102216644c59dae5baed380d84830c").unwrap();
            let (r, s, pk, digest) = simulate_signature_for_sk(sk);

            let witness = ECDSARecoverableSignatureWitness {
                r,
                s,
                v: false
            };

            let signature = ECDSASignature::allocate_from_witness(cs, &scalar_params, Some(witness))?;
            let digest = FieldElement::new_allocated(cs, Some(digest), &scalar_params)?;

            let mut address = [Byte::<E>::empty(); 20];
            for (i, b) in eth_address.into_iter().enumerate() {
                let b = Byte::constant(b);
                address[i] = b;
            }

            let is_valid = ctx.verify_for_ethereum_address(
                cs, 
                signature, 
                Some(pk), 
                digest, 
                4,
                &address
            )?;
            dbg!(is_valid.get_value());
            assert!(is_valid.get_value().unwrap());
        }

        ctx.enforce(cs)?;

        let used = cs.n() - n;
        let used = used / num_items;
        println!("Used {} gates per signature for {} signatures for address verification", used, num_items);

        assert!(cs.is_satisfied());

        Ok(())
    }
}