use super::read_view::MemoryKey;
use super::*;
use crate::glue::code_unpacker_sha256::memory_query_updated::RawMemoryQuery;

// Since we do opcode decoding, or mask it, and in the encoding procedure we
// use tables and explicit range checks, then we may be ok just allocate all the chunks as unchecked,
// but for now we do it in a checked way!

// DO NOT make pub to avoid breaking invariants

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct CodeReadQuery<E: Engine> {
    timestamp: UInt32<E>,
    memory_page: UInt32<E>,
    memory_index: UInt32<E>,
    pub(crate) u64_word_0: UInt64<E>,
    pub(crate) u64_word_1: UInt64<E>,
    pub(crate) u64_word_2: UInt64<E>,
    pub(crate) u64_word_3: UInt64<E>,
}

impl<E: Engine> CodeReadQuery<E> {
    pub(crate) fn into_raw_query<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<RawMemoryQuery<E>, SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.u64_word_0.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.u64_word_1.inner, shifts[64]);
        lc.add_assign_number_with_coeff(&self.u64_word_2.inner, shifts[128]);
        let value = lc.into_num(cs)?;
        let new = RawMemoryQuery {
            timestamp: self.timestamp,
            memory_page: self.memory_page,
            memory_index: self.memory_index,
            rw_flag: Boolean::constant(false),
            value_residual: self.u64_word_3,
            value,
            value_is_ptr: Boolean::constant(false),
        };

        Ok(new)
    }

    pub(crate) fn from_key_and_value_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        key: MemoryKey<E>,
        value: Option<BigUint>,
    ) -> Result<Self, SynthesisError> {
        use num_traits::ToPrimitive;

        // decompose witness if we know it
        let mut words = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let u64_word_3 = words.pop().unwrap().map(|el| el.to_u64().unwrap());
        let u64_word_2 = words.pop().unwrap().map(|el| el.to_u64().unwrap());
        let u64_word_1 = words.pop().unwrap().map(|el| el.to_u64().unwrap());
        let u64_word_0 = words.pop().unwrap().map(|el| el.to_u64().unwrap());

        let u64_word_0 = UInt64::allocate(cs, u64_word_0)?;
        let u64_word_1 = UInt64::allocate(cs, u64_word_1)?;
        let u64_word_2 = UInt64::allocate(cs, u64_word_2)?;
        let u64_word_3 = UInt64::allocate(cs, u64_word_3)?;

        let MemoryKey {
            timestamp,
            memory_page,
            memory_index,
        } = key;

        let new = Self {
            timestamp,
            memory_page,
            memory_index,
            u64_word_0,
            u64_word_1,
            u64_word_2,
            u64_word_3,
        };

        Ok(new)
    }
}
