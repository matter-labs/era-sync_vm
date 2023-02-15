use super::read_view::MemoryKey;
use super::*;
use crate::glue::code_unpacker_sha256::memory_query_updated::RawMemoryQuery;
use crate::vm::primitives::register_view::*;

// DO NOT make pub to avoid breaking invariants

use crate::traits::CSWitnessable;
use cs_derive::*;

#[derive(Derivative, CSWitnessable)]
#[derivative(Clone, Debug)]
pub struct MemoryWriteQuery<E: Engine> {
    pub timestamp: UInt32<E>,
    pub memory_page: UInt32<E>,
    pub memory_index: UInt32<E>,
    pub lowest_128: UInt128<E>,
    pub u64_word_2: UInt64<E>,
    pub u64_word_3: UInt64<E>,
    pub value_is_ptr: Boolean,
}

impl<E: Engine> MemoryWriteQuery<E> {
    pub(crate) fn into_raw_query<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<RawMemoryQuery<E>, SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.lowest_128.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.u64_word_2.inner, shifts[128]);
        let value = lc.into_num(cs)?;
        let new = RawMemoryQuery {
            timestamp: self.timestamp,
            memory_page: self.memory_page,
            memory_index: self.memory_index,
            rw_flag: Boolean::constant(true),
            value_residual: self.u64_word_3,
            value,
            value_is_ptr: self.value_is_ptr,
        };

        Ok(new)
    }

    pub(crate) fn from_key_and_value_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        key: MemoryKey<E>,
        register_output: Register<E>,
    ) -> Result<Self, SynthesisError> {
        use num_traits::ToPrimitive;

        let [lowest_128, highest_128] = register_output.inner;

        let tmp = highest_128
            .get_value()
            .map(|el| (el as u64, (el >> 64) as u64));
        let (u64_word_2, u64_word_3) = match tmp {
            Some((a, b)) => (Some(a), Some(b)),
            _ => (None, None),
        };

        // we do not need to range check everything, only N-1 ut of N elements in LC

        let u64_word_2 = UInt64::allocate_unchecked(cs, u64_word_2)?;
        let u64_word_3 = UInt64::allocate(cs, u64_word_3)?;

        let shifts = compute_shifts::<E::Fr>();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&u64_word_2.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&u64_word_3.inner, shifts[64]);
        lc.add_assign_number_with_coeff(&highest_128.inner, minus_one);

        let MemoryKey {
            timestamp,
            memory_page,
            memory_index,
        } = key;

        let new = Self {
            timestamp,
            memory_page,
            memory_index,
            lowest_128,
            u64_word_2,
            u64_word_3,
            value_is_ptr: register_output.is_ptr,
        };

        Ok(new)
    }
}
