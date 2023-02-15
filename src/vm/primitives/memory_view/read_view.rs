use super::*;
use crate::scheduler::queues::RawMemoryQuery;
use super::super::register_view::*;


// Important note on this structure: we can make sure that
// - this query will not go into the queue if it's not executed (so if opcode doesn't touch a memory)
// - if it's executed then it will be a feeded all the way into the function that decomposes a selected
// value into the "view", thus range checks all the uint128 parts that we use unchecked here
// So we only need to ensure that all parts are range checked if all the above actually executes. It automatically
// will guarantee us that lowest128 is indeed 128 bits, and that u64_word_2 + (u64_word_3 << 64) is also 128 bits,
// so we only need to ensure that e.g. u64_word_3 is 128 bits

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct MemoryKey<E: Engine> {
    pub timestamp: UInt32<E>,
    pub memory_markers: [Boolean; 2],
    pub memory_page: UInt32<E>,
    pub memory_index: UInt16<E>,
}

impl<E: Engine> MemoryKey<E> {
    pub fn uninitialized() -> Self {
        MemoryKey {
            timestamp: UInt32::<E>::zero(),
            memory_markers: [Boolean::constant(false); 2],
            memory_page: UInt32::<E>::zero(),
            memory_index: UInt16::<E>::zero(),
        }
    }
}

// DO NOT make pub to avoid breaking invariants

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct MemoryReadQuery<E: Engine> {
    timestamp: UInt32<E>,
    memory_markers: [Boolean; 2],
    memory_page: UInt32<E>,
    memory_index: UInt16<E>,
    lowest_128: UInt128<E>,
    u64_word_2: UInt64<E>,
    u64_word_3: UInt64<E>,
}

impl<E: Engine> MemoryReadQuery<E> {
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

    pub(crate) fn from_key_and_value_witness<CS: ConstraintSystem<E>>(cs: &mut CS, key: MemoryKey<E>, value: Option<BigUint>) -> Result<Self, SynthesisError> {
        use num_traits::ToPrimitive;

        // decompose witness if we know it
        let mut words = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let u64_word_3 = words.pop().unwrap().map(|el| el.to_u64().unwrap());
        let u64_word_2 = words.pop().unwrap().map(|el| el.to_u64().unwrap());
        let u64_word_1 = words.pop().unwrap();
        let u64_word_0 = words.pop().unwrap();

        // only range check the word 3, and make a wittness for the rest
        let lowest_128 = match (u64_word_0, u64_word_1) {
            (Some(u64_word_0), Some(u64_word_1)) => {
                let tmp = u64_word_0 + (u64_word_1 << 64u64);

                Some(tmp.to_u128().unwrap())
            },
            _ => None
        };

        let lowest_128 = UInt128::allocate_unchecked(cs, lowest_128)?;
        let u64_word_2 = UInt64::allocate(cs, u64_word_2)?;
        let u64_word_3 = UInt64::allocate(cs, u64_word_3)?;

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

    pub(crate) fn into_register_value<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Register<E>, SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.u64_word_2.inner, shifts[0]);
        lc.add_assign_number_with_coeff(&self.u64_word_3.inner, shifts[64]);
        let highest_128 = UInt128::from_num_unchecked(lc.into_num(cs)?);

        let result = Register {
            inner: [self.lowest_128, highest_128]
        };

        Ok(result)
    }
}

