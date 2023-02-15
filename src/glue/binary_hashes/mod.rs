use crate::bellman::SynthesisError;
use crate::data_structures::markers::*;
use crate::derivative::*;
use crate::ff::*;
use crate::pairing::*;
use crate::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::plonk::circuit::Assignment;

use crate::circuit_structures::byte::*;
use crate::circuit_structures::traits::*;
use crate::circuit_structures::utils::*;
use franklin_crypto::rescue::RescueHashParams;

use crate::franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::Keccak256Gadget;
use franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget;

pub fn sha256<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    input: &[Byte<E>],
) -> Result<[Byte<E>; 32], SynthesisError> {
    assert!(input.len() > 0);
    let sha256_gadget = Sha256Gadget::new(cs, None, None, false, false, 0, "")?;

    let output = sha256_gadget.sha256_from_bytes_to_bytes(cs, &input)?;

    Ok(output)
}

pub fn keccak256<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    keccak_gadget: &Keccak256Gadget<E>,
    input: &[Byte<E>],
) -> Result<[Byte<E>; 32], SynthesisError> {
    assert!(input.len() > 0);
    let output = keccak_gadget.digest_from_bytes(cs, &input)?;
    assert_eq!(output.len(), 4);

    let mut output_as_bytes = [Byte::zero(); 32];
    for (idx, word) in output.into_iter().enumerate() {
        let bytes = num_into_bytes_le(cs, word, 64)?;
        assert_eq!(bytes.len(), 8);
        output_as_bytes[idx * 8..(idx + 1) * 8].copy_from_slice(&bytes);
    }

    Ok(output_as_bytes)
}

pub trait CircuitBinaryHasher<E: Engine>: Clone {
    fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError>;
    fn hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError>;
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct Sha256Hasher<E: Engine> {
    gadget: Sha256Gadget<E>,
}

impl<E: Engine> CircuitBinaryHasher<E> for Sha256Hasher<E> {
    fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let reused_table_name =
            crate::franklin_crypto::plonk::circuit::tables::RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME;

        let gadget = Sha256Gadget::new(cs, None, None, false, true, 16, reused_table_name)?;

        let new = Self { gadget };

        Ok(new)
    }

    fn hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        self.gadget.sha256_from_bytes_to_bytes(cs, &input)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct Keccak256Hasher<E: Engine> {
    gadget: Keccak256Gadget<E>,
}

impl<E: Engine> CircuitBinaryHasher<E> for Keccak256Hasher<E> {
    fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let reused_table_name =
            crate::franklin_crypto::plonk::circuit::tables::RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME;

        let gadget = Keccak256Gadget::new(cs, None, None, None, None, true, &reused_table_name)?;

        let new = Self { gadget };

        Ok(new)
    }

    fn hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        keccak256(cs, &self.gadget, input)
    }
}

pub fn pack_field_elements_for_chunked_data_repacking<F: PrimeField>(
    elements: &[F],
    chunk_size: usize,
    max_chunks: usize,
) -> Vec<u8> {
    assert!(elements.len() <= max_chunks);
    let mut buffer = [0u8; 32];
    let mut items_encodings = vec![];

    for el in elements.iter() {
        // we use BE encoding
        let repr = el.into_repr();
        repr.write_be(&mut buffer[..]).unwrap();
        items_encodings.push(buffer);
    }

    let mut bytes = vec![0u8; chunk_size * max_chunks];
    let mut it = items_encodings.into_iter().rev();
    for chunk in bytes.chunks_exact_mut(chunk_size).rev() {
        if let Some(el) = it.next() {
            chunk.copy_from_slice(&el[(32 - chunk_size)..]);
        }
    }

    bytes
}
