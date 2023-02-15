use crate::{
    circuit_structures::byte::Byte,
    franklin_crypto::{
        bellman::{plonk::better_better_cs::cs::ConstraintSystem, Engine, SynthesisError},
        plonk::circuit::byte::IntoBytes,
        plonk::circuit::hashes_with_tables::keccak::gadgets::Keccak256Gadget,
        plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget,
    },
};

pub trait CircuitTreeHasher<E: Engine>: Sized {
    fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError>;

    fn hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError>;

    fn leaf_hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        leaf: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        self.hash(cs, leaf)
    }

    fn node_hash<CS: ConstraintSystem<E>, const ARITY: usize>(
        &self,
        cs: &mut CS,
        nodes: &[[Byte<E>; 32]; ARITY],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        let mut combined_leaf = vec![Byte::zero(); ARITY * 32];

        for idx in 0..ARITY {
            combined_leaf[idx * 32..(idx + 1) * 32].copy_from_slice(&nodes[idx]);
        }
        self.hash(cs, &combined_leaf)
    }
}

pub struct CircuitKeccakTreeHasher<E: Engine> {
    hasher: Keccak256Gadget<E>,
}

impl<E: Engine> CircuitKeccakTreeHasher<E> {
    fn hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        let output = self.hasher.digest_from_bytes(cs, &input)?;
        assert_eq!(output.len(), 4);

        let mut output_as_bytes = [Byte::zero(); 32];
        for (idx, word) in output.into_iter().enumerate() {
            use crate::utils::num_into_bytes_le;
            let bytes = num_into_bytes_le(cs, word, 64)?;
            assert_eq!(bytes.len(), 8);
            output_as_bytes[idx * 8..(idx + 1) * 8].copy_from_slice(&bytes);
        }

        Ok(output_as_bytes)
    }
}

impl<E: Engine> CircuitTreeHasher<E> for CircuitKeccakTreeHasher<E> {
    fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let reused_table_name =
            crate::franklin_crypto::plonk::circuit::tables::RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME;

        let gadget = Keccak256Gadget::new(cs, None, None, None, None, true, &reused_table_name)?;

        let new = Self { hasher: gadget };

        Ok(new)
    }

    fn hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        self.hash(cs, input)
    }
}

pub struct CircuitSha256TreeHasher<E: Engine> {
    pub hasher: Sha256Gadget<E>,
}

impl<E: Engine> CircuitTreeHasher<E> for CircuitSha256TreeHasher<E> {
    fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let sha256_gadget = Sha256Gadget::new(cs, None, None, false, false, 0, "")?;

        Ok(Self {
            hasher: sha256_gadget,
        })
    }

    fn hash<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input: &[Byte<E>],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        self.hasher.sha256_from_bytes_to_bytes(cs, input)
    }
}
