use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::Keccak256Gadget;

use super::*;

pub const NUM_SHARDS: usize = 2;

// Data that represents a pure state
#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Copy, Debug)]
pub struct PerShardState<E: Engine> {
    pub enumeration_counter: UInt64<E>,
    pub state_root: Bytes32<E>,
}

// Data that is something like STF(BlockPassthroughData, BlockMetaParameters) -> (BlockPassthroughData, BlockAuxilaryOutput)
#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct BlockPassthroughData<E: Engine> {
    pub per_shard_states: [PerShardState<E>; NUM_SHARDS],
}

// Defining some system parameters that are configurable
#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct BlockMetaParameters<E: Engine> {
    pub bootloader_code_hash: Bytes32<E>,
    pub default_aa_code_hash: Bytes32<E>,
    pub zkporter_is_available: Boolean,
}

// This is the information that represents artifacts only meaningful for this block, that will not be used for any
// next block
#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct BlockAuxilaryOutput<E: Engine> {
    pub l1_messages_root: Bytes32<E>,
    pub l1_messages_linear_hash: Bytes32<E>,
    // pub events_root_hash: Bytes32<E>,
    // pub events_linear_hash: Bytes32<E>,
    pub rollup_initital_writes_pubdata_hash: Bytes32<E>,
    pub rollup_repeated_writes_pubdata_hash: Bytes32<E>,
}

#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct BlockHeader<E: Engine> {
    pub previous_block_content_hash: Bytes32<E>,
    pub new_block_content_hash: Bytes32<E>,
}

// only contains information about this block (or any one block in general),
// without anything about the previous one
#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct BlockContentHeader<E: Engine> {
    pub block_data: BlockPassthroughData<E>,
    pub block_meta: BlockMetaParameters<E>,
    pub auxilary_output: BlockAuxilaryOutput<E>,
}

impl<E: Engine> PerShardState<E> {
    pub fn into_flattened_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        // everything is BE
        let mut result = vec![];
        let enumeration_index_be = self.enumeration_counter.into_be_bytes(cs)?;
        result.extend(enumeration_index_be);
        result.extend_from_slice(&self.state_root.inner);

        Ok(result)
    }
}

impl<E: Engine> BlockPassthroughData<E> {
    pub fn into_flattened_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        // everything is BE
        let mut result = vec![];
        for el in self.per_shard_states.iter() {
            let be_bytes = el.into_flattened_bytes(cs)?;
            result.extend(be_bytes);
        }

        Ok(result)
    }
}

impl<E: Engine> BlockMetaParameters<E> {
    pub fn into_flattened_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        // everything is BE
        let mut result = vec![];
        let zk_porter_byte =
            Byte::from_num_unconstrained(cs, Num::from_boolean_is(self.zkporter_is_available));
        result.push(zk_porter_byte);

        result.extend_from_slice(&self.bootloader_code_hash.inner);
        result.extend_from_slice(&self.default_aa_code_hash.inner);

        Ok(result)
    }
}

impl<E: Engine> BlockAuxilaryOutput<E> {
    pub fn into_flattened_bytes<CS: ConstraintSystem<E>>(
        &self,
        _cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        // everything is BE
        let mut result = vec![];
        result.extend_from_slice(&self.l1_messages_root.inner);
        result.extend_from_slice(&self.l1_messages_linear_hash.inner);
        result.extend_from_slice(&self.rollup_initital_writes_pubdata_hash.inner);
        result.extend_from_slice(&self.rollup_repeated_writes_pubdata_hash.inner);

        Ok(result)
    }
}

pub fn keccak_output_into_bytes<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    keccak_output: Vec<Num<E>>,
) -> Result<[Byte<E>; 32], SynthesisError> {
    assert_eq!(keccak_output.len(), 4);

    let mut result = vec![];
    let bytes0 = UInt64::from_num_unchecked(keccak_output[0]).into_le_bytes(cs)?;
    result.extend(bytes0);
    let bytes1 = UInt64::from_num_unchecked(keccak_output[1]).into_le_bytes(cs)?;
    result.extend(bytes1);
    let bytes2 = UInt64::from_num_unchecked(keccak_output[2]).into_le_bytes(cs)?;
    result.extend(bytes2);
    let bytes3 = UInt64::from_num_unchecked(keccak_output[3]).into_le_bytes(cs)?;
    result.extend(bytes3);

    Ok(result.try_into().unwrap())
}

impl<E: Engine> BlockContentHeader<E> {
    pub fn into_formal_block_hash<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<([Byte<E>; 32], ([Byte<E>; 32], [Byte<E>; 32], [Byte<E>; 32])), SynthesisError>
    {
        // everything is BE
        let block_data = self.block_data.into_flattened_bytes(cs)?;
        let block_meta = self.block_meta.into_flattened_bytes(cs)?;
        let auxilary_output = self.auxilary_output.into_flattened_bytes(cs)?;

        let keccak_gadget = Keccak256Gadget::new(
            cs,
            None,
            None,
            None,
            None,
            true,
            RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME,
        )?;

        let block_data_hash = keccak_gadget.digest_from_bytes(cs, &block_data)?;
        let block_data_hash = keccak_output_into_bytes(cs, block_data_hash)?;

        let block_meta_hash = keccak_gadget.digest_from_bytes(cs, &block_meta)?;
        let block_meta_hash = keccak_output_into_bytes(cs, block_meta_hash)?;

        let auxilary_output_hash = keccak_gadget.digest_from_bytes(cs, &auxilary_output)?;
        let auxilary_output_hash = keccak_output_into_bytes(cs, auxilary_output_hash)?;

        let block_hash = Self::formal_block_hash_from_partial_hashes(
            cs,
            block_data_hash,
            block_meta_hash,
            auxilary_output_hash,
        )?;

        Ok((
            block_hash,
            (block_data_hash, block_meta_hash, auxilary_output_hash),
        ))
    }

    pub fn formal_block_hash_from_partial_hashes<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        block_data_hash: [Byte<E>; 32],
        block_meta_hash: [Byte<E>; 32],
        auxilary_output_hash: [Byte<E>; 32],
    ) -> Result<[Byte<E>; 32], SynthesisError> {
        let keccak_gadget = Keccak256Gadget::new(
            cs,
            None,
            None,
            None,
            None,
            true,
            RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME,
        )?;

        let mut concatenated = vec![];
        concatenated.extend(block_data_hash);
        concatenated.extend(block_meta_hash);
        concatenated.extend(auxilary_output_hash);

        let block_header_hash = keccak_gadget.digest_from_bytes(cs, &concatenated)?;
        let block_header_hash = keccak_output_into_bytes(cs, block_header_hash)?;

        Ok(block_header_hash)
    }
}
