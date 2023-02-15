use super::*;
use crate::scheduler::queues::RawMemoryQuery;
use super::read_view::MemoryKey;
use super::super::register_view::*;

// DO NOT make pub to avoid breaking invariants

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct MemoryWriteQuery<E: Engine> {
    timestamp: UInt32<E>,
    memory_markers: [Boolean; 2],
    memory_page: UInt32<E>,
    memory_index: UInt16<E>,
    lowest_128: UInt128<E>,
    u64_word_2: UInt64<E>,
    u64_word_3: UInt64<E>,
}

impl<E: Engine> MemoryWriteQuery<E> {
    pub(crate) fn into_raw_query<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<RawMemoryQuery<E>, SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.lowest_128.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.u64_word_2.inner, shifts[128]);
        let value = lc.into_num(cs)?;
        let new = RawMemoryQuery {
            timestamp_meta: Boolean::constant(true),
            timestamp: self.timestamp,
            memory_markers: self.memory_markers,
            memory_page: self.memory_page,
            memory_index: self.memory_index,
            rw_flag: Boolean::constant(false),
            value_residual: self.u64_word_3,
            value,
        };

        Ok(new)
    }

    pub(crate) fn from_key_and_value_witness<CS: ConstraintSystem<E>>(cs: &mut CS, key: MemoryKey<E>, register_output: Register<E>) -> Result<Self, SynthesisError> {
        use num_traits::ToPrimitive;

        let [lowest_128, highest_128] = register_output.inner;

        let tmp = highest_128.get_value().map(|el| (el as u64, (el >> 64) as u64));
        let (u64_word_2, u64_word_3) = match tmp {
            Some((a, b)) => (Some(a), Some(b)),
            _ => (None, None)
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
            memory_markers,
            memory_page,
            memory_index,
        } = key;

        let new = Self {
            timestamp,
            memory_markers,
            memory_page,
            memory_index,
            lowest_128,
            u64_word_2,
            u64_word_3
        };

        Ok(new)
    }
}

