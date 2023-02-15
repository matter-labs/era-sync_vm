use super::*;
use cs_derive::*;

pub mod input;

use crate::glue::traits::get_vec_vec_witness;
use crate::glue::traits::get_vec_vec_witness_raw_with_hint_on_more_in_subset;
use crate::glue::traits::get_vec_witness_raw;
use crate::precompiles::*;
use crate::scheduler::queues::FixedWidthEncodingGenericQueueState;
use crate::scheduler::queues::FullSpongeLikeQueueState;

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct EcrecoverPrecompileCallParams<E: Engine> {
    pub input_page: UInt32<E>,
    pub input_offset: UInt32<E>,
    pub output_page: UInt32<E>,
    pub output_offset: UInt32<E>,
}

impl<E: Engine> EcrecoverPrecompileCallParams<E> {
    pub fn empty() -> Self {
        Self {
            input_page: UInt32::<E>::zero(),
            input_offset: UInt32::<E>::zero(),
            output_page: UInt32::<E>::zero(),
            output_offset: UInt32::<E>::zero(),
        }
    }

    pub fn from_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        encoding: UInt256<E>,
    ) -> Result<Self, SynthesisError> {
        let input_encoding = encoding.inner[0];
        let output_encoding = encoding.inner[1];
        let pages_encoding = encoding.inner[2];

        let shifts = compute_shifts::<E::Fr>();
        let input_chunks = input_encoding.decompose_into_uint16_in_place(cs)?;

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&input_chunks[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&input_chunks[1].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let input_offset = UInt32::from_num_unchecked(num);

        let output_chunks = output_encoding.decompose_into_uint16_in_place(cs)?;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&output_chunks[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&output_chunks[1].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let output_offset = UInt32::from_num_unchecked(num);

        let page_chunks = pages_encoding.decompose_into_uint16_in_place(cs)?;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&page_chunks[0].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&page_chunks[1].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let input_page = UInt32::from_num_unchecked(num);

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&page_chunks[2].inner, shifts[0]);
        lc.add_assign_number_with_coeff(&page_chunks[3].inner, shifts[16]);
        let num = lc.into_num(cs)?;
        let output_page = UInt32::from_num_unchecked(num);

        let new = Self {
            input_page,
            input_offset,
            output_page,
            output_offset,
        };

        Ok(new)
    }
}

pub use self::input::*;
use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQueriesQueue;
use crate::scheduler::queues::StorageLogQueue;
use crate::vm::vm_cycle::memory_view::write_query::MemoryWriteQuery;

use super::*;
use crate::franklin_crypto::plonk::circuit::bigint_new::*;
use crate::franklin_crypto::plonk::circuit::curve_new::*;
// characteristics of the base field for secp curve
use crate::secp256k1::fq::Fq as Secp256Fq;
// order of group of points for secp curve
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::*;
use crate::secp256k1::fr::Fr as Secp256Fr;
use num_bigint::BigUint;
use num_traits::One;

const CHUNK_BITLEN: usize = 64;
const SECP_B_COEF: u64 = 7;
const EXCEPTION_FLAGS_ARR_LEN: usize = 4;
const NUM_MEMORY_READS_PER_CYCLE: usize = 3;
const X_POWERS_ARR_LEN: usize = 256;
const UNPADDED_KECCAK_INPUT_WORDS_LEN: usize = 8;
const KECCAK_DIGEST_WORDS_SIZE: usize = 3;

// assume that constructed field element is not zero
// if this is not satisfied - set the result to be F::one
fn convert_uint256_to_field_element<'a, E: Engine, F: PrimeField, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    elem: &UInt256<E>,
    rns_strategy: &'a RnsParameters<E, F>,
    exceptions: &mut Vec<Boolean>,
) -> Result<FieldElement<'a, E, F>, SynthesisError> {
    let raw_limbs = elem
        .inner
        .into_iter()
        .map(|x| x.inner)
        .collect::<Vec<Num<E>>>();
    let mut fe = unsafe {
        FieldElement::<E, F>::alloc_from_limbs_unchecked(cs, &raw_limbs, &rns_strategy, false)?
    };
    let is_zero = FieldElement::is_zero(&mut fe, cs)?;
    exceptions.push(is_zero);
    FieldElement::conditionally_select(cs, &is_zero, &FieldElement::one(&rns_strategy), &fe)
}

fn ecrecover_precompile_inner_routine<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    G: GenericCurveAffine + rand::Rand,
>(
    cs: &mut CS,
    recid: &UInt32<E>,
    r_as_u64x4: &UInt256<E>,
    s_as_u64x4: &UInt256<E>,
    message_hash_as_u64x4: &UInt256<E>,
    secp_p_as_u64x4: &UInt256<E>,
    secp_n_as_u64x4: &UInt256<E>,
    b_coef_in_external_field: &FieldElement<'a, E, G::Base>,
    valid_x_in_external_field: &FieldElement<'a, E, G::Base>,
    valid_t_in_external_field: &FieldElement<'a, E, G::Base>,
    minus_one_in_external_field: &mut FieldElement<'a, E, G::Base>,
    rns_strategy_for_base_field: &'a RnsParameters<E, G::Base>,
    rns_strategy_for_scalar_field: &'a RnsParameters<E, G::Scalar>,
    keccak_gadget: &Keccak256Gadget<E>,
) -> Result<(Boolean, UInt256<E>), SynthesisError>
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    let mut two = E::Fr::one();
    two.double();
    let two_inv = two.inverse().unwrap();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    let mut minus_two = minus_one.clone();
    minus_two.double();

    let table = cs.get_table(BITWISE_LOGICAL_OPS_TABLE_NAME)?;
    let dummy = CS::get_dummy_variable();
    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let mut exception_flags = Vec::with_capacity(EXCEPTION_FLAGS_ARR_LEN);

    // recid = (x_overflow ? 2 : 0) | (secp256k1_fe_is_odd(&r.y) ? 1 : 0)
    // The point X = (x, y) we are going to recover is not known at the start, but it is strongly related to r.
    // This is because x = r + kn for some integer k, where x is an element of the field F_q . In other words, x < q.
    // (here n is the order of group of points on elleptic curve)
    // For secp256k1 curve values of q and n are relatively close, that is,
    // the probability of a random element of Fq being greater than n is about 1/{2^128}.
    // This in turn means that the overwhelming majority of r determine a unique x, however some of them determine
    // two: x = r and x = r + n. If x_overflow flag is set than x = r + n
    let x_overflow = Boolean::Is(AllocatedBit::alloc(
        cs,
        recid.get_value().map(|x| x & 0b10 != 0),
    )?);
    let y_is_odd = Boolean::Is(AllocatedBit::alloc(
        cs,
        recid.get_value().map(|x| x & 0b1 != 0),
    )?);
    let mut lc = LinearCombination::zero();
    lc.add_assign_boolean_with_coeff(&x_overflow, two.clone());
    lc.add_assign_boolean_with_coeff(&y_is_odd, E::Fr::one());
    lc.add_assign_number_with_coeff(&recid.inner, minus_one.clone());
    lc.enforce_zero(cs)?;

    let (r_plus_n_as_u64x4, of) = r_as_u64x4.add(cs, &secp_n_as_u64x4)?;
    let mut x_as_u64x4 =
        UInt256::conditionally_select(cs, &x_overflow, &r_plus_n_as_u64x4, &r_as_u64x4)?;
    let error = Boolean::and(cs, &x_overflow, &of)?;
    exception_flags.push(error);

    // we handle x separately as it is the only element of base field of a curve (no a scalar field element!)
    // check that x < q - order of base point on Secp256 curve
    // if it is not actually the case - mask x to be zero
    let (_res, is_in_range) = x_as_u64x4.sub(cs, &secp_p_as_u64x4)?;
    x_as_u64x4 = x_as_u64x4.mask(cs, &is_in_range)?;
    exception_flags.push(is_in_range.not());
    let raw_x_limbs = x_as_u64x4
        .inner
        .into_iter()
        .map(|x| x.inner)
        .collect::<Vec<Num<E>>>();
    let x_fe = unsafe {
        FieldElement::<E, G::Base>::alloc_from_limbs_unchecked(
            cs,
            &raw_x_limbs,
            &rns_strategy_for_base_field,
            true,
        )?
    };

    let mut r_fe = convert_uint256_to_field_element::<E, G::Scalar, CS>(
        cs,
        &r_as_u64x4,
        &rns_strategy_for_scalar_field,
        &mut exception_flags,
    )?;
    let mut s_fe = convert_uint256_to_field_element::<E, G::Scalar, CS>(
        cs,
        &s_as_u64x4,
        &rns_strategy_for_scalar_field,
        &mut exception_flags,
    )?;
    // NB: although it is not strictly an exception we also assume that hash is never zero as field element
    let mut message_hash_fe = convert_uint256_to_field_element::<E, G::Scalar, CS>(
        cs,
        &message_hash_as_u64x4,
        &rns_strategy_for_scalar_field,
        &mut exception_flags,
    )?;

    // curve equation is y^2 = x^3 + b
    // we compute t = r^3 + b and check if t is a quadratic residue or not.
    // we do this by computing Legendre symbol (t, p) = t^[(p-1)/2] (mod p)
    // p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
    // n = (p-1)/ 2 = 2^255 - 2^31 - 2^8 - 2^7 - 2^6 - 2^5 - 2^3 - 1
    // we have to compute t^b = t^{2^255} / ( t^{2^31} * t^{2^8} * t^{2^7} * t^{2^6} * t^{2^5} * t^{2^3} * t)
    // if t is not a quadratic residue we return error and replace x by another value that will make
    // t = x^3 + b a quadratic residue

    let mut t = x_fe.square(cs)?;
    t = t.mul(cs, &x_fe)?;
    t = t.add_with_reduction(
        cs,
        &b_coef_in_external_field.clone(),
        ReductionStatus::Loose,
    )?;
    let t_is_zero = FieldElement::is_zero(&mut t, cs)?;
    exception_flags.push(t_is_zero);

    // if t is zero then just mask
    let t = FieldElement::<E, G::Base>::conditionally_select(
        cs,
        &t_is_zero,
        &valid_t_in_external_field,
        &t,
    )?;

    // array of powers of t of the form t^{2^i} starting from i = 0 to 255
    let mut t_powers = Vec::with_capacity(X_POWERS_ARR_LEN);
    t_powers.push(t);

    for _ in 1..X_POWERS_ARR_LEN {
        let prev = t_powers.last().cloned().unwrap();
        t_powers.push(prev.square(cs)?);
    }
    let mut acc = t_powers[0].clone();
    for idx in [3, 5, 6, 7, 8, 31].into_iter() {
        acc = acc.mul(cs, &t_powers[idx])?;
    }
    let mut legendre_symbol = t_powers[255].div(cs, &acc)?;

    let t_is_nonresidue =
        FieldElement::<E, G::Base>::equals(cs, &mut legendre_symbol, minus_one_in_external_field)?;
    exception_flags.push(t_is_nonresidue);
    // unfortunately, if t is found to be a quadratic nonresidue, we can't simply let x to be zero,
    // because then t_new = 7 is again a quadratic nonresidue. So, in this case we let x to be 9, then
    // t = 16 is a quadratic residue
    let x = FieldElement::<E, G::Base>::conditionally_select(
        cs,
        &t_is_nonresidue,
        &valid_x_in_external_field,
        &x_fe,
    )?;
    let mut t = FieldElement::<E, G::Base>::conditionally_select(
        cs,
        &t_is_nonresidue,
        &valid_t_in_external_field,
        &t_powers[0],
    )?;
    // we find the value of y, s.t. y^2 = t, and such that y is odd if y_is_odd flag is set and even otherwise
    let y_wit = match (t.get_field_value(), y_is_odd.get_value()) {
        (Some(fr), Some(y_is_odd)) => {
            let mut tmp = fr
                .sqrt()
                .expect(&format!("should be a quadratic residue: {}", fr));
            let tmp_is_odd = tmp.into_repr().as_ref()[0] & 1u64 != 0;
            if tmp_is_odd ^ y_is_odd {
                tmp.negate();
            }
            Some(tmp)
        }
        (_, _) => None,
    };
    let (y, y_decomposition) =
        FieldElement::<E, G::Base>::alloc_ext(cs, y_wit, &rns_strategy_for_base_field)?;
    {
        // enforce that y^2 == t
        let mut y_squared = y.square(cs)?;
        FieldElement::<E, G::Base>::enforce_equal(cs, &mut t, &mut y_squared)?;
    }
    {
        // enforce that y is odd <=> y_is_odd flag is set
        // this equal to the constraint: (lowest_limb - y_is_odd) / 2 is range [0, 1 << RANGE_TABLE_WIDTH)
        // let q = (lowest_limb - y_is_odd) / 2, then 2*q + y_odd = lowest_limb
        // we construct the following gate: [lowest_limb, q, q_and_lowest_limb, y_is_odd]
        // NOTE: the whole trick works only if we use BITWISE_XOR table as our range table
        let a = y_decomposition.get_vars()[0];
        let b = AllocatedNum::alloc(cs, || {
            let mut tmp = a.get_value().grab()?;
            tmp.sub_assign(&y_is_odd.get_value_in_field::<E>().grab()?);
            tmp.mul_assign(&two_inv);
            Ok(tmp)
        })?;

        let a_xor_b = match (a.get_value(), b.get_value()) {
            (Some(a_val), Some(b_val)) => {
                let res = table.query(&[a_val, b_val])?;
                AllocatedNum::alloc(cs, || Ok(res[0]))?
            }
            (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
        };

        // we construct the following gate: [lowest_limb, q, q_and_lowest_limb, y_is_odd] := [a, b, c, d]
        // 2 * b = a - d => a - 2 * b - d = 0
        let y_is_odd_var = y_is_odd.get_variable().unwrap().get_variable();
        let vars = [
            a.get_variable(),
            b.get_variable(),
            a_xor_b.get_variable(),
            y_is_odd_var,
        ];
        let coeffs = [E::Fr::one(), minus_two.clone(), E::Fr::zero(), minus_one];

        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
        for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
        cs.end_gates_batch_for_step()?;
    }

    // now we are going to compute the public key Q = (x, y) determined by the formula:
    // Q = (s * X - hash * G) / r which is equivalent to r * Q = s * X - hash * G
    // current implementation of point by scalar multiplications doesn't support multiplication by zero
    // so we check that all s, r, hash are not zero (as FieldElements):
    // if any of them is zero we reject the signature and in circuit itself replace all zero variables by ones
    let mut x_point = unsafe { AffinePoint::<E, G>::from_xy_unchecked(x, y) };
    let s_x = x_point.mul_by_scalar_for_prime_order_curve(cs, &mut s_fe)?;

    let mut generator = AffinePoint::<E, G>::constant(G::one(), &rns_strategy_for_base_field);
    let hash_g = generator.mul_by_scalar_for_prime_order_curve(cs, &mut message_hash_fe)?;

    let mut rhs_proj = s_x.sub(cs, &hash_g)?;
    let (mut rhs_affine, is_point_at_infty) =
        rhs_proj.convert_to_affine_or_default(cs, &generator)?;
    exception_flags.push(is_point_at_infty);

    let q_wit: Option<G> = match (r_fe.get_field_value(), rhs_affine.get_value()) {
        (Some(r_val), Some(pt)) => {
            // Q = 1/r * pt
            let r_inv_val = r_val.inverse().unwrap();
            let mut res = pt.into_projective();
            res.mul_assign(r_inv_val.into_repr());
            Some(res.into_affine())
        }
        _ => None,
    };
    let (mut q, q_x_chunks, q_y_chunks) =
        AffinePoint::alloc_ext(cs, q_wit, &rns_strategy_for_base_field)?;
    q.enforce_if_normalized(cs)?;

    let lhs_proj = q.mul_by_scalar_for_prime_order_curve(cs, &mut r_fe)?;
    // NB: we assume that the difference is NEVER point at infinity
    // it is justified by the fact their difference must be a public key Q which is never point at infinity
    let mut lhs_affine = unsafe { lhs_proj.convert_to_affine(cs)? };
    // AffinePoint::<E, G>::enforce_equal(cs, &mut lhs_affine, &mut rhs_affine)?;

    let any_exception = smart_or(cs, &exception_flags[..])?;
    let comparison_result = AffinePoint::<E, G>::equals(cs, &mut lhs_affine, &mut rhs_affine)?;
    // if no exceptions have happened then LHS == RHS must hold
    can_not_be_false_if_flagged(cs, &comparison_result, &any_exception.not())?;

    let mut q_x_chunks_be: Vec<_> = q_x_chunks
        .get_vars()
        .into_iter()
        .map(|el| Byte::from_num_unconstrained(cs, Num::Variable(*el)))
        .collect();
    q_x_chunks_be.reverse();
    let mut q_y_chunks_be: Vec<_> = q_y_chunks
        .get_vars()
        .into_iter()
        .map(|el| Byte::from_num_unconstrained(cs, Num::Variable(*el)))
        .collect();
    q_y_chunks_be.reverse();

    // our PK format is serialized as 32 bytes for X coordinate BE + same for Y
    let it = q_x_chunks_be.into_iter().chain(q_y_chunks_be.into_iter());

    let to_hash: Vec<_> = it.collect();
    let hash_digest = keccak_gadget.digest_from_bytes(cs, &to_hash[..])?;
    use crate::scheduler::block_header::keccak_output_into_bytes;
    let mut digest_bytes = keccak_output_into_bytes(cs, hash_digest)?;

    // digest is 32 bytes, but we need only 20 to recover address
    digest_bytes[0..12].copy_from_slice(&[Byte::empty(); 12]); // empty out top bytes
    let written_value_unmasked = UInt256::from_be_bytes_fixed(cs, &digest_bytes)?;

    let written_value = written_value_unmasked.mask(cs, &any_exception.not())?;

    Ok((any_exception.not(), written_value))
}

use crate::glue::aux_byte_markers::aux_byte_for_precompile_call;

pub fn ecrecover_function_entry_point<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    witness: Option<EcrecoverCircuitInstanceWitness<E>>,
    round_function: &R,
    limit: usize,
) -> Result<AllocatedNum<E>, SynthesisError> {
    use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
    use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

    let columns3 = vec![
        PolyIdentifier::VariablesPolynomial(0),
        PolyIdentifier::VariablesPolynomial(1),
        PolyIdentifier::VariablesPolynomial(2),
    ];

    if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
        let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            BitwiseLogicTable::new(&name, 8),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(bitwise_logic_table)?;
    };

    inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    type G = crate::secp256k1::PointAffine;

    assert!(limit <= u32::MAX as usize);
    let keccak_gadget = Keccak256Gadget::new(cs, None, None, None, None, false, "")?;

    let precompile_address = UInt160::<E>::from_uint(u160::from_u64(
        zkevm_opcode_defs::system_params::ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS as u64,
    ));
    let aux_byte_for_precompile = aux_byte_for_precompile_call::<E>();

    let secp_p_as_u64x4 = UInt256::<E>::constant(
        franklin_crypto::plonk::circuit::bigint_new::bigint::repr_to_biguint::<Secp256Fq>(
            &Secp256Fq::char(),
        ),
    );
    let secp_n_as_u64x4 = UInt256::<E>::constant(
        franklin_crypto::plonk::circuit::bigint_new::bigint::repr_to_biguint::<Secp256Fr>(
            &Secp256Fr::char(),
        ),
    );
    assert_eq!(CHUNK_BITLEN, 64);
    let rns_strategy_for_base_field =
        RnsParameters::<E, <G as GenericCurveAffine>::Base>::new_optimal(cs, CHUNK_BITLEN);
    let rns_strategy_for_scalar_field =
        RnsParameters::<E, <G as GenericCurveAffine>::Scalar>::new_optimal(cs, CHUNK_BITLEN);

    let one_in_external_field =
        FieldElement::<E, <G as GenericCurveAffine>::Base>::one(&rns_strategy_for_base_field);
    let mut minus_one_in_external_field = one_in_external_field.negate(cs)?;
    let b_coef_in_external_field = FieldElement::<E, <G as GenericCurveAffine>::Base>::constant(
        u64_to_fe::<<G as GenericCurveAffine>::Base>(SECP_B_COEF),
        &rns_strategy_for_base_field,
    );
    let valid_x_in_external_field = FieldElement::<E, <G as GenericCurveAffine>::Base>::constant(
        u64_to_fe::<<G as GenericCurveAffine>::Base>(9),
        &rns_strategy_for_base_field,
    );
    let valid_t_in_external_field = FieldElement::<E, <G as GenericCurveAffine>::Base>::constant(
        u64_to_fe::<<G as GenericCurveAffine>::Base>(9 + SECP_B_COEF),
        &rns_strategy_for_base_field,
    );

    let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
    let requests_queue_witness = project_ref!(witness, requests_queue_witness).cloned();
    let mut memory_reads_witness = project_ref!(witness, memory_reads_witness).cloned();

    let mut structured_input =
        EcrecoverCircuitInputOutput::alloc_ignoring_outputs(cs, structured_input_witness.clone())?;

    let requests_queue_from_fsm_input = StorageLogQueue::from_raw_parts(
        cs,
        structured_input.hidden_fsm_input.log_queue_state.head_state,
        structured_input.hidden_fsm_input.log_queue_state.tail_state,
        structured_input.hidden_fsm_input.log_queue_state.num_items,
    )?;

    let requests_queue_from_passthrough = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .initial_log_queue_state
            .head_state,
        structured_input
            .observable_input
            .initial_log_queue_state
            .tail_state,
        structured_input
            .observable_input
            .initial_log_queue_state
            .num_items,
    )?;

    let mut requests_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &requests_queue_from_passthrough,
        &requests_queue_from_fsm_input,
    )?;

    if let Some(wit) = requests_queue_witness {
        requests_queue.witness = wit;
    }

    let memory_queue_from_fsm_input = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input.hidden_fsm_input.memory_queue_state.head,
        structured_input.hidden_fsm_input.memory_queue_state.tail,
        structured_input.hidden_fsm_input.memory_queue_state.length,
    )?;

    let memory_queue_from_passthrough = MemoryQueriesQueue::from_raw_parts(
        cs,
        structured_input.observable_input.initial_memory_state.head,
        structured_input.observable_input.initial_memory_state.tail,
        structured_input
            .observable_input
            .initial_memory_state
            .length,
    )?;

    let mut memory_queue = MemoryQueriesQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &memory_queue_from_passthrough,
        &memory_queue_from_fsm_input,
    )?;

    for _cycle in 0..limit {
        let is_empty = requests_queue.is_empty(cs)?;
        let request = requests_queue.pop_first(cs, &is_empty.not(), round_function)?;
        let mut precompile_call_params =
            EcrecoverPrecompileCallParams::from_encoding(cs, request.key)?;
        let timestamp_to_use_for_read = request.timestamp;
        let (timestamp_to_use_for_write, of) = timestamp_to_use_for_read.increment_checked(cs)?;
        Boolean::enforce_equal(cs, &of, &Boolean::constant(false))?;

        use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQuery;

        Num::conditionally_enforce_equal(
            cs,
            &is_empty.not(),
            &request.aux_byte.inner,
            &aux_byte_for_precompile.inner,
        )?;
        Num::conditionally_enforce_equal(
            cs,
            &is_empty.not(),
            &request.address.inner,
            &precompile_address.inner,
        )?;

        let mut read_values = [UInt256::zero(); 4];
        let mut read_values_le_bytes = [[Num::zero(); 32]; 4];

        for idx in 0..4 {
            let (memory_query_witness, _) = get_vec_vec_witness_raw_with_hint_on_more_in_subset(
                &mut memory_reads_witness,
                BigUint::from(0u64),
            );
            let (u256_value, le_bytes) =
                UInt256::alloc_from_biguint_and_return_u8_chunks(cs, memory_query_witness)?;
            let mut memory_query = MemoryQuery::<E>::empty();
            memory_query.timestamp = timestamp_to_use_for_read;
            memory_query.memory_page = precompile_call_params.input_page;
            memory_query.memory_index = precompile_call_params.input_offset;
            memory_query.rw_flag = Boolean::constant(false);
            memory_query.value = u256_value;

            read_values[idx] = u256_value;
            read_values_le_bytes[idx] = le_bytes;

            let memory_query = memory_query.into_raw_query(cs)?;
            let _ = memory_queue.push(cs, &memory_query, &is_empty.not(), round_function)?;

            precompile_call_params.input_offset = precompile_call_params
                .input_offset
                .increment_unchecked(cs)?;
        }

        let [message_hash_as_u64x4, _v, r_as_u64x4, s_as_u64x4] = read_values;
        let [_, v_bytes, _, _] = read_values_le_bytes;
        let recid = UInt32::from_num_unchecked(v_bytes[0]);

        let (success, written_value) = ecrecover_precompile_inner_routine::<E, CS, G>(
            cs,
            &recid,
            &r_as_u64x4,
            &s_as_u64x4,
            &message_hash_as_u64x4,
            &secp_p_as_u64x4,
            &secp_n_as_u64x4,
            &b_coef_in_external_field,
            &valid_x_in_external_field,
            &valid_t_in_external_field,
            &mut minus_one_in_external_field,
            &rns_strategy_for_base_field,
            &rns_strategy_for_scalar_field,
            &keccak_gadget,
        )?;

        let mut success_as_u256 = UInt256::zero();
        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&success, E::Fr::one());
        success_as_u256.inner[0] = UInt64::from_num_unchecked(lc.into_num(cs)?);

        let success_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: precompile_call_params.output_page,
            memory_index: precompile_call_params.output_offset,
            rw_flag: Boolean::constant(true),
            value: success_as_u256,
            value_is_ptr: Boolean::constant(false),
        };
        let success_query = success_query.into_raw_query(cs)?;

        precompile_call_params.output_offset = precompile_call_params
            .output_offset
            .increment_unchecked(cs)?;
        let _ = memory_queue.push(cs, &success_query, &is_empty.not(), round_function)?;
        let value_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: precompile_call_params.output_page,
            memory_index: precompile_call_params.output_offset,
            rw_flag: Boolean::constant(true),
            value: written_value,
            value_is_ptr: Boolean::constant(false),
        };
        let value_query = value_query.into_raw_query(cs)?;

        precompile_call_params.output_offset = precompile_call_params
            .output_offset
            .increment_unchecked(cs)?;
        let _ = memory_queue.push(cs, &value_query, &is_empty.not(), round_function)?;
    }

    // form the final state
    let done = requests_queue.is_empty(cs)?;
    structured_input.completion_flag = done;
    structured_input.observable_output = PrecompileFunctionOutputData::empty();

    let final_memory_state = memory_queue.into_state();
    let final_requets_state = requests_queue.into_state();

    structured_input.observable_output.final_memory_state =
        FullSpongeLikeQueueState::conditionally_select(
            cs,
            &structured_input.completion_flag,
            &final_memory_state,
            &structured_input.observable_output.final_memory_state,
        )?;

    structured_input.hidden_fsm_output.log_queue_state = final_requets_state;
    structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = structured_input_witness {
            assert_eq!(circuit_result, passed_input);
        }
    }

    use crate::inputs::ClosedFormInputCompactForm;
    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    // dbg!(compact_form.create_witness());
    use crate::glue::optimizable_queue::commit_encodable_item;
    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();
    let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;

    Ok(public_input)
}
