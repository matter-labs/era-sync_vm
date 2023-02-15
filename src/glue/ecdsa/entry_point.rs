use traits::get_vec_witness_raw;

use super::*;
use super::recover::*;
use super::signature::*;

use crate::scheduler::{QueueProcessorStructuredInput, QueueProcessorStructuredInputWitness};
use crate::scheduler::queues::EcdsaVerificationQueue;
use crate::glue::optimizable_queue::commit_encodable_item;
use crate::franklin_crypto::plonk::circuit::bigint::{FieldElement, RnsParameters};
use crate::scheduler::queues::FixedWidthEncodingGenericQueueWitness;
use crate::scheduler::queues::EcdsaVerificationRecord;

use super::curve::curve::PointAffine as Secp256Affine;
use super::curve::fq::Fq as Secp256Fq;
use super::curve::fr::Fr as Secp256Fr;
use crate::scheduler::queues::ecdsa_request::*;

pub fn ecdsa_prover_entry_point<
    E: Engine, 
    CS: ConstraintSystem<E>, 
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>, 
>(
    cs: &mut CS,
    input_witness: Option<QueueProcessorStructuredInputWitness<E>>,
    queue_witness: Option<FixedWidthEncodingGenericQueueWitness<E, EcdsaVerificationRecord<E>, ECDSA_VERIFICATION_RECORD_ENCODING_LEN>>,
    signature_witnesses: Option<Vec<(ECDSARecoverableSignatureWitness<Secp256Affine>, Secp256Affine)>>,
    scalar_rns_params: RnsParameters<E, Secp256Fr>,
    base_field_rns_params: RnsParameters<E, Secp256Fq>,
    round_function: &R,
    limit: usize
) -> Result<(), SynthesisError> {
    let input = QueueProcessorStructuredInput::alloc_from_witness(cs, input_witness)?;
    let mut queue = EcdsaVerificationQueue::<E>::empty();
    queue.head_state = input.queue_head;
    queue.tail_state = input.queue_tail;
    queue.num_items = input.queue_length;
    if let Some(wit) = queue_witness {
        queue.witness = wit;
    }

    ecdsa_prover_prover_inner(
        cs,
        queue,
        signature_witnesses,
        scalar_rns_params,
        base_field_rns_params,
        round_function,
        limit
    )?;

    let input_commitment = commit_encodable_item(cs, &input, round_function)?;
    let input_commitment_witness = input_commitment.get_value();
    let public_input = AllocatedNum::alloc_input(
        cs,
        || input_commitment_witness.grab()
    )?;
    public_input.enforce_equal(cs, &input_commitment.get_variable())?;

    Ok(())
}

pub fn ecdsa_prover_prover_inner<
    E: Engine, 
    CS: ConstraintSystem<E>, 
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>, 
>(
    cs: &mut CS,
    mut queue: EcdsaVerificationQueue<E>,
    mut signature_witnesses: Option<Vec<(ECDSARecoverableSignatureWitness<Secp256Affine>, Secp256Affine)>>,
    scalar_rns_params: RnsParameters<E, Secp256Fr>,
    base_field_rns_params: RnsParameters<E, Secp256Fq>,
    round_function: &R,
    limit: usize
) -> Result<(), SynthesisError> {
    queue.enforce_to_be_not_empty(cs)?;

    let mut ctx = ECRecoverContext::<E, Secp256Affine, 8>::new_for_signed_multiplications(8, &scalar_rns_params, &base_field_rns_params);
    for _ in 0..limit {
        let execute = queue.is_empty(cs)?.not();
        let request = queue.pop_first(cs, &execute, round_function)?;
        let wit = get_vec_witness_raw(&mut signature_witnesses, 
            (ECDSARecoverableSignatureWitness::empty(), Secp256Affine::one())
        );
        let (signature, pk) = match wit {
            Some(wit) => {
                let (sig, pk) = wit;
                (Some(sig), Some(pk))
            },
            _ => {(None, None)}
        };
        let signature = ECDSASignature::allocate_from_witness(cs, &scalar_rns_params, signature)?;
        let EcdsaVerificationRecord { address, message } = request;
        let message_bytes_le = message.inner;
        assert_eq!(message_bytes_le.len(), 32);
        let address_bytes = crate::utils::num_into_bytes_be(cs, address.inner, 160)?;
        assert_eq!(address_bytes.len(), 20);
        use std::convert::TryInto;
        let address: [Byte<E>; 20] = address_bytes.try_into().expect("length must match");

        let digest = allocate_field_element_from_le_bytes(cs, &message_bytes_le, &scalar_rns_params)?;

        let is_valid = ctx.verify_for_ethereum_address(
            cs, 
            signature, 
            pk, 
            digest, 
            4,
            &address
        )?;

        can_not_be_false_if_flagged(cs, &is_valid, &execute)?;
    }

    queue.enforce_to_be_empty(cs)?;
    ctx.enforce(cs)?;

    Ok(())
}

fn allocate_field_element_from_le_bytes<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    F: PrimeField
>(
    cs: &mut CS,
    le_bytes: &[Byte<E>],
    rns_params: &'a RnsParameters<E, F>,
) -> Result<FieldElement<'a, E, F>, SynthesisError> {
    assert!(rns_params.binary_limbs_params.limb_size_bits % 8 == 0);
    let take_elements = rns_params.binary_limbs_params.limb_size_bits / 8;
    let shifts = compute_shifts::<E::Fr>();
    let mut limbs = vec![];
    for chunk in le_bytes.chunks(take_elements) {
        let mut lc = LinearCombination::zero();
        for (i, el) in chunk.iter().enumerate() {
            lc.add_assign_number_with_coeff(&el.inner, shifts[i*8]);
        }
        let limb = lc.into_num(cs)?;
        limbs.push(limb);
    }
    
    let element = FieldElement::allocate_from_single_limb_witnesses_in_field(
        cs,
        &limbs,
        rns_params
    )?;

    Ok(element)
}
