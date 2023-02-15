use super::*;
use crate::glue::traits::*;
use crate::vm::primitives::{UInt16, UInt32};
use cs_derive::*;
use num_traits::Zero;
// We accumulate memory queries and then use a standard validity argument

#[derive(
    Derivative,
    CSWitnessable,
    CSAllocatable,
    CSEqual,
    CSSelectable,
    FixedLengthEncodableExt,
    FixedLengthDecodableExt,
)]
#[EncodingLength = "2"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct PackedMemoryQuery<E: Engine> {
    pub timestamp_meta: Boolean,
    pub timestamp: UInt32<E>,
    pub memory_key: UInt64<E>,
    pub rw_flag: Boolean,
    pub value_residual: UInt64<E>,
    pub value: Num<E>,
}

impl<E: Engine> PackedMemoryQuery<E> {
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 2], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let el0 = self.value;

        let mut shift = 0;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.value_residual.inner, shifts[shift]);
        shift += 64;
        lc.add_assign_boolean_with_coeff(&self.rw_flag, shifts[shift]);
        shift += 1;
        lc.add_assign_number_with_coeff(&self.memory_key.inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.timestamp.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_boolean_with_coeff(&self.timestamp_meta, shifts[shift]);
        shift += 1;

        assert!(shift <= E::Fr::CAPACITY as usize);

        let el1 = lc.into_num(cs)?;

        Ok([el0, el1])
    }
}

#[derive(
    Derivative,
    CSWitnessable,
    CSAllocatable,
    CSEqual,
    CSSelectable,
    FixedLengthEncodableExt,
    FixedLengthDecodableExt,
)]
#[EncodingLength = "2"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct RawMemoryQuery<E: Engine> {
    pub timestamp_meta: Boolean,
    pub timestamp: UInt32<E>,
    pub memory_markers: [Boolean; 2],
    pub memory_page: UInt32<E>,
    pub memory_index: UInt16<E>,
    pub rw_flag: Boolean,
    pub value_residual: UInt64<E>,
    pub value: Num<E>,
}

impl<E: Engine> RawMemoryQuery<E> {
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 2], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let el0 = self.value;

        let mut shift = 0;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.value_residual.inner, shifts[shift]);
        shift += 64;
        lc.add_assign_boolean_with_coeff(&self.rw_flag, shifts[shift]);
        shift += 1;
        // NOTE: we pack is as it would be compatible with PackedMemoryQuery later on
        lc.add_assign_number_with_coeff(&self.memory_index.inner, shifts[shift]);
        shift += 16;
        lc.add_assign_number_with_coeff(&self.memory_page.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_boolean_with_coeff(&self.memory_markers[0], shifts[shift]);
        shift += 1;
        lc.add_assign_boolean_with_coeff(&self.memory_markers[1], shifts[shift]);
        shift += 1;

        shift += 14;
        // ------------
        lc.add_assign_number_with_coeff(&self.timestamp.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_boolean_with_coeff(&self.timestamp_meta, shifts[shift]);
        shift += 1;

        assert!(shift <= E::Fr::CAPACITY as usize);

        let el1 = lc.into_num(cs)?;

        Ok([el0, el1])
    }
}

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct MemoryQuery<E: Engine> {
    pub timestamp_meta: Boolean,
    pub timestamp: UInt32<E>,
    pub memory_markers: [Boolean; 2],
    pub memory_page: UInt32<E>,
    pub memory_index: UInt16<E>,
    pub rw_flag: Boolean,
    pub value: UInt256<E>,
}

impl<E: Engine> MemoryQuery<E> {
    pub fn empty() -> Self {
        Self {
            timestamp_meta: Boolean::constant(false),
            timestamp: UInt32::zero(),
            memory_markers: [Boolean::constant(false); 2],
            memory_page: UInt32::zero(),
            memory_index: UInt16::zero(),
            rw_flag: Boolean::constant(false),
            value: UInt256::zero(),
        }
    }
    pub fn into_raw_query<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<RawMemoryQuery<E>, SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let residual = self.value.inner[3];

        let mut shift = 0;
        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&self.value.inner[0].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.value.inner[1].inner, shifts[shift]);
        shift += 64;
        lc.add_assign_number_with_coeff(&self.value.inner[2].inner, shifts[shift]);
        shift += 64;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let value = lc.into_num(cs)?;

        let query = RawMemoryQuery {
            timestamp_meta: self.timestamp_meta,
            timestamp: self.timestamp,
            memory_markers: self.memory_markers,
            memory_page: self.memory_page,
            memory_index: self.memory_index,
            rw_flag: self.rw_flag,
            value_residual: residual,
            value,
        };

        Ok(query)
    }
}

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct CodeQuery<E: Engine> {
    pub timestamp_meta: Boolean,
    pub timestamp: UInt32<E>,
    pub memory_page: UInt32<E>,
    pub memory_index: UInt16<E>,
    pub rw_flag: Boolean,
    pub value: Num<E>,
}

impl<E: Engine> CodeQuery<E> {
    pub fn into_raw_query(&self) -> RawMemoryQuery<E> {
        let query = RawMemoryQuery {
            timestamp_meta: self.timestamp_meta,
            timestamp: self.timestamp,
            memory_markers: [Boolean::constant(false); 2],
            memory_page: self.memory_page,
            memory_index: self.memory_index,
            rw_flag: self.rw_flag,
            value_residual: UInt64::zero(),
            value: self.value,
        };

        query
    }
}

pub type MemoryQueriesQueue<E, const SW: usize, const AW: usize> =
    FixedWidthEncodingSpongeLikeQueue<E, RawMemoryQuery<E>, 2, SW, AW>;
