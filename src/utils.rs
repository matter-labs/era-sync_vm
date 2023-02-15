use crate::bellman::SynthesisError;
use crate::ff::*;
use franklin_crypto::bellman::bn256::Bn256;
use rescue_poseidon::{CustomGate, HashParams, RescueParams};

pub const fn bit_width_to_bitmask(width: usize) -> u64 {
    (1u64 << width) - 1
}

#[macro_export]
macro_rules! project {
    ($w: expr) => {
        $w.clone()
    };
    ($w: ident, $field: ident) => {
        $w.as_ref().map(|el| el.$field.clone())
    };
    ($w: expr, $field: expr) => {
        $w.as_ref().map(|el| el.$field.clone())
    };
}

#[macro_export]
macro_rules! project_ref {
    ($w: expr) => {
        &w
    };
    ($w: ident, $field: ident) => {
        $w.as_ref().map(|el| &(el.$field))
    };
    ($w: expr, $field: expr) => {
        $w.as_ref().map(|el| &(el.$field))
    };
}

pub fn log2_floor(value: usize) -> u32 {
    if value.is_power_of_two() {
        value.trailing_zeros()
    } else {
        value.next_power_of_two().trailing_zeros() - 1
    }
}

pub const AWIDTH_VALUE: usize = 2;
pub const SWIDTH_VALUE: usize = 3;

pub fn bn254_rescue_params() -> RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE> {
    // let mut params = RescueParams::default();
    let mut params = RescueParams::specialized_for_num_rounds(5, 100);
    params.use_custom_gate(CustomGate::QuinticWidth4);

    params
}

pub fn u16_to_fe<F: PrimeField>(value: u16) -> F {
    u64_to_fe(value as u64)
}

pub fn u32_to_fe<F: PrimeField>(value: u32) -> F {
    u64_to_fe(value as u64)
}

pub fn u64_to_fe<F: PrimeField>(value: u64) -> F {
    let mut repr = F::Repr::default();
    repr.as_mut()[0] = value;

    F::from_repr(repr).unwrap()
}

pub fn u128_to_fe<F: PrimeField>(value: u128) -> F {
    let mut repr = F::Repr::default();
    repr.as_mut()[0] = value as u64;
    repr.as_mut()[1] = (value >> 64) as u64;

    F::from_repr(repr).unwrap()
}

pub fn fe_to_u64<F: PrimeField>(value: F) -> u64 {
    let repr = value.into_repr();

    repr.as_ref()[0]
}

pub fn fe_to_u128<F: PrimeField>(value: F) -> u128 {
    let repr = value.into_repr();
    let mut shift = 0;
    let mut value = 0u128;
    for limb in repr.as_ref().iter().take(2) {
        value += (*limb as u128) << shift;
        shift += 64;
    }

    value
}

pub fn u64_to_le_bits(value: u64, limit: Option<usize>) -> Vec<bool> {
    let limit = if let Some(limit) = limit { limit } else { 64 };

    let mut bits: Vec<bool> = BitIterator::new(&[value]).collect();
    bits.reverse();
    bits.truncate(limit);

    bits
}

pub fn u8_to_le_bits(value: u8) -> [bool; 8] {
    let mut result = [false; 8];
    let mut value = value;
    for idx in 0..8 {
        result[idx] = value & 1u8 == 1u8;
        value >>= 1;
    }

    result
}

pub fn fe_to_le_bits<F: PrimeField>(value: F, limit: Option<usize>) -> Vec<bool> {
    let limit = if let Some(limit) = limit {
        limit
    } else {
        F::NUM_BITS as usize
    };

    let mut bits: Vec<bool> = BitIterator::new(&value.into_repr()).collect();
    bits.reverse();
    bits.truncate(limit);

    bits
}
#[derive(Clone, Copy)]
struct ZeroPaddingBuffer<'a>(&'a [u8]);

impl<'a> std::io::Read for ZeroPaddingBuffer<'a> {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_vectored(&mut self, _bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_to_end(&mut self, _buf: &mut Vec<u8>) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_to_string(&mut self, _buf: &mut String) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        let bytes_available = self.0.len();
        let len = buf.len();
        if bytes_available >= len {
            let (to_read, leftover) = self.0.split_at(len);
            buf.copy_from_slice(&*to_read);

            self.0 = leftover;
        } else {
            buf[..bytes_available].copy_from_slice(&self.0);
            for b in buf[bytes_available..].iter_mut() {
                *b = 0u8;
            }
            self.0 = &[];
        }
        Ok(())
    }
    fn by_ref(&mut self) -> &mut Self
    where
        Self: Sized,
    {
        self
    }
    fn bytes(self) -> std::io::Bytes<Self>
    where
        Self: Sized,
    {
        unimplemented!()
    }
    fn chain<R: std::io::Read>(self, _next: R) -> std::io::Chain<Self, R>
    where
        Self: Sized,
    {
        unimplemented!()
    }
    fn take(self, _limit: u64) -> std::io::Take<Self>
    where
        Self: Sized,
    {
        unimplemented!()
    }
}

#[derive(Clone, Copy)]
struct ZeroPrePaddingBuffer<'a>(&'a [u8], usize);

impl<'a> std::io::Read for ZeroPrePaddingBuffer<'a> {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_vectored(&mut self, _bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_to_end(&mut self, _buf: &mut Vec<u8>) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_to_string(&mut self, _buf: &mut String) -> std::io::Result<usize> {
        unimplemented!()
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        let bytes_available = self.0.len();
        let padding_available = self.1;
        let len = buf.len();
        if padding_available >= len {
            self.1 -= len;
            for b in buf.iter_mut() {
                *b = 0u8;
            }
        } else {
            let (dst_to_zero, dst_to_read_to) = buf.split_at_mut(self.1);
            self.1 = 0;
            for b in dst_to_zero.iter_mut() {
                *b = 0u8;
            }
            let len = dst_to_read_to.len();
            if len >= bytes_available {
                let (to_read, leftover) = self.0.split_at(len);
                dst_to_read_to.copy_from_slice(&*to_read);
                self.0 = leftover;
            } else {
                let midpoint = len - bytes_available;
                dst_to_read_to[midpoint..].copy_from_slice(&self.0);
                for b in dst_to_read_to[..midpoint].iter_mut() {
                    *b = 0u8;
                }
                self.0 = &[];
            }
        }

        Ok(())
    }
    fn by_ref(&mut self) -> &mut Self
    where
        Self: Sized,
    {
        self
    }
    fn bytes(self) -> std::io::Bytes<Self>
    where
        Self: Sized,
    {
        unimplemented!()
    }
    fn chain<R: std::io::Read>(self, _next: R) -> std::io::Chain<Self, R>
    where
        Self: Sized,
    {
        unimplemented!()
    }
    fn take(self, _limit: u64) -> std::io::Take<Self>
    where
        Self: Sized,
    {
        unimplemented!()
    }
}

#[track_caller]
pub fn pack_be_bytes_to_fe<F: PrimeField>(bytes: &[u8]) -> Result<F, SynthesisError> {
    let mut repr = F::zero().into_repr();
    let expected_len = repr.as_ref().len() * 8;
    assert!(bytes.len() <= expected_len);
    let padding = expected_len - bytes.len();
    let buff = ZeroPrePaddingBuffer(&bytes, padding);
    repr.read_be(buff)
        .map_err(|_| SynthesisError::Unsatisfiable)?;
    let el = F::from_repr(repr).map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(el)
}

#[track_caller]
pub fn pack_le_bytes_to_fe<F: PrimeField>(bytes: &[u8]) -> Result<F, SynthesisError> {
    let buff = ZeroPaddingBuffer(&bytes);
    let mut repr = F::zero().into_repr();
    repr.read_le(buff)
        .map_err(|_| SynthesisError::Unsatisfiable)?;
    let el = F::from_repr(repr).map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(el)
}

#[track_caller]
pub fn fe_to_be_bytes<F: PrimeField>(el: &F) -> Result<Vec<u8>, SynthesisError> {
    let mut buffer = vec![];
    let repr = el.into_repr();
    repr.write_be(&mut buffer)
        .map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(buffer)
}

#[track_caller]
pub fn fe_to_le_bytes<F: PrimeField>(el: &F) -> Result<Vec<u8>, SynthesisError> {
    let mut buffer = vec![];
    let repr = el.into_repr();
    repr.write_le(&mut buffer)
        .map_err(|_| SynthesisError::Unsatisfiable)?;

    Ok(buffer)
}

pub fn compute_shifts<F: PrimeField>() -> Vec<F> {
    let mut result = Vec::with_capacity(F::CAPACITY as usize);
    let mut el = F::one();
    result.push(el);
    for _ in 1..F::CAPACITY {
        el.double();
        result.push(el);
    }

    result
}

pub fn next_multiple_of(mut value: usize, of: usize) -> usize {
    let remainder = value % of;
    if remainder != 0 {
        value += of - remainder;
    }

    value
}

use std::{iter, mem};
pub trait IdentifyFirstLast: Iterator + Sized {
    fn identify_first_last(self) -> Iter<Self>;
}

impl<I> IdentifyFirstLast for I
where
    I: Iterator,
{
    fn identify_first_last(self) -> Iter<Self> {
        Iter(true, self.peekable())
    }
}

pub struct Iter<I>(bool, iter::Peekable<I>)
where
    I: Iterator;

impl<I> Iterator for Iter<I>
where
    I: Iterator,
{
    type Item = (bool, bool, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let first = mem::replace(&mut self.0, false);
        self.1.next().map(|e| (first, self.1.peek().is_none(), e))
    }
}

pub(crate) use crate::franklin_crypto::plonk::circuit::byte::{
    num_into_bytes_be, num_into_bytes_le,
};

pub trait BigArraySerde<'de>: Sized {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer;
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>;
}

impl<'de, T, const N: usize> BigArraySerde<'de> for [T; N]
where
    T: serde::Serialize + serde::Deserialize<'de>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeTuple;
        let mut seq = serializer.serialize_tuple(N)?;
        for elem in &self[..] {
            seq.serialize_element(elem)?;
        }
        seq.end()
    }

    fn deserialize<D>(deserializer: D) -> Result<[T; N], D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct ArrayVisitor<T, const M: usize> {
            element: std::marker::PhantomData<T>,
        }

        impl<'de, T, const M: usize> serde::de::Visitor<'de> for ArrayVisitor<T, M>
        where
            T: serde::Deserialize<'de>,
        {
            type Value = [T; M];

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str(&format!("an array of length {}", M))
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<[T; M], A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut arr = Vec::with_capacity(M);
                for i in 0..M {
                    let el = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
                    arr.push(el);
                }
                let arr: [T; M] = arr
                    .try_into()
                    .map_err(|_| serde::de::Error::invalid_length(M, &self))?;

                Ok(arr)
            }
        }

        let visitor = ArrayVisitor::<_, N> {
            element: std::marker::PhantomData,
        };
        deserializer.deserialize_tuple(N, visitor)
    }
}

pub struct BigArrayRefWrapper<'de, B: BigArraySerde<'de>>(&'de B);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayRefWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

pub struct BigArrayWrapper<'de, B: BigArraySerde<'de>>(B, std::marker::PhantomData<&'de ()>);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de, B: BigArraySerde<'de>> serde::Deserialize<'de> for BigArrayWrapper<'de, B> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let new = B::deserialize(deserializer)?;

        Ok(Self(new, std::marker::PhantomData))
    }
}
