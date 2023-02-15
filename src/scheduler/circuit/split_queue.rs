use super::*;
use std::convert::TryInto;

pub fn split_queue<
    E: Engine,
    CS: ConstraintSystem<E>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
    const NUM_CHUNKS: usize,
    const MAX_CHUNK_LENGTH: usize,
>(
    cs: &mut CS,
    queue: FixedWidthEncodingGenericQueue<E, I, N>,
    chunks_sizes: Option<[u32; NUM_CHUNKS]>,
) -> Result<[FixedWidthEncodingGenericQueue<E, I, N>; NUM_CHUNKS], SynthesisError> {
    assert!(NUM_CHUNKS > 0, "some splitting must happen");
    if N == 1 {
        // just ensure that we are below the max splitting
        let (_, uf) = UInt32::from_uint(MAX_CHUNK_LENGTH as u32).sub(cs, &queue.len())?;
        Boolean::enforce_equal(cs, &uf, &Boolean::constant(false))?;

        let result: [FixedWidthEncodingGenericQueue<E, I, N>; NUM_CHUNKS] =
            vec![queue].try_into().unwrap();

        return Ok(result);
    }
    let mut result = vec![];
    let mut remainder = queue;
    if let Some(sizes) = chunks_sizes.as_ref() {
        assert_eq!(
            *sizes.last().unwrap(),
            0,
            "last element of chunk sizes is unused and must be zero"
        );
    }
    for i in 0..(NUM_CHUNKS - 1) {
        let split_point = chunks_sizes.as_ref().map(|el| el[i]);
        if let Some(split_point) = split_point.as_ref() {
            assert!(
                *split_point <= MAX_CHUNK_LENGTH as u32,
                "trying to split too large chunk"
            );
        }
        let split_point = UInt32::allocate(cs, split_point)?;
        let (first, second) = remainder.split(cs, split_point)?;
        remainder = second;
        result.push(first);
    }
    // check that length of the final piece is smaller than maximum size
    let (_, uf) = UInt32::from_uint(MAX_CHUNK_LENGTH as u32).sub(cs, &remainder.len())?;
    Boolean::enforce_equal(cs, &uf, &Boolean::constant(false))?;
    result.push(remainder);

    let result: [FixedWidthEncodingGenericQueue<E, I, N>; NUM_CHUNKS] =
        result.try_into().expect("length must match");

    Ok(result)
}

pub fn split_sponge_like_queue<
    E: Engine,
    CS: ConstraintSystem<E>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
    const NUM_CHUNKS: usize,
    const MAX_CHUNK_LENGTH: usize,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    queue: FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>,
    chunks_sizes: Option<[u32; NUM_CHUNKS]>,
) -> Result<[FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>; NUM_CHUNKS], SynthesisError>
{
    assert!(NUM_CHUNKS > 0, "some splitting must happen");
    if N == 1 {
        // just ensure that we are below the max splitting
        let (_, uf) = UInt32::from_uint(MAX_CHUNK_LENGTH as u32).sub(cs, &queue.len())?;
        Boolean::enforce_equal(cs, &uf, &Boolean::constant(false))?;

        let result: [FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>; NUM_CHUNKS] =
            vec![queue].try_into().unwrap();

        return Ok(result);
    }
    let mut result = vec![];
    let mut remainder = queue;
    if let Some(sizes) = chunks_sizes.as_ref() {
        assert_eq!(
            *sizes.last().unwrap(),
            0,
            "last element of chunk sizes is unused and must be zero"
        );
    }
    for i in 0..(NUM_CHUNKS - 1) {
        let split_point = chunks_sizes.as_ref().map(|el| el[i]);
        if let Some(split_point) = split_point.as_ref() {
            assert!(
                *split_point <= MAX_CHUNK_LENGTH as u32,
                "trying to split too large chunk"
            );
        }
        let split_point = UInt32::allocate(cs, split_point)?;
        let (first, second) = remainder.split(cs, split_point)?;
        remainder = second;
        result.push(first);
    }
    // check that length of the final piece is smaller than maximum size
    let (_, uf) = UInt32::from_uint(MAX_CHUNK_LENGTH as u32).sub(cs, &remainder.len())?;
    Boolean::enforce_equal(cs, &uf, &Boolean::constant(false))?;
    result.push(remainder);

    let result: [FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>; NUM_CHUNKS] =
        result.try_into().expect("length must match");

    Ok(result)
}

pub fn join_queues<
    E: Engine,
    CS: ConstraintSystem<E>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
>(
    cs: &mut CS,
    first: FixedWidthEncodingGenericQueue<E, I, N>,
    second: FixedWidthEncodingGenericQueue<E, I, N>,
    execute: &Boolean,
) -> Result<FixedWidthEncodingGenericQueue<E, I, N>, SynthesisError> {
    let mut tmp = vec![];
    let v = Num::equals(cs, &first.get_tail_state(), &second.get_head_state())?;
    tmp.push(v);
    // check that length of the final piece is smaller than maximum size
    let (final_len, of) = first.len().add(cs, &second.len())?;
    tmp.push(of.not());
    let valid = smart_and(cs, &tmp)?;
    can_not_be_false_if_flagged(cs, &valid, &execute)?;

    let mut result = FixedWidthEncodingGenericQueue::<E, I, N>::empty();
    result.head_state = first.head_state;
    result.tail_state = second.tail_state;
    result.num_items = final_len;
    result.witness = first.witness;
    result.witness.wit.extend(second.witness.wit);

    Ok(result)
}

pub fn join_sponge_like_queues<
    E: Engine,
    CS: ConstraintSystem<E>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
    const AWIDTH: usize,
    const SWIDTH: usize,
>(
    cs: &mut CS,
    first: FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>,
    second: FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>,
    execute: &Boolean,
) -> Result<FixedWidthEncodingSpongeLikeQueue<E, I, N, AWIDTH, SWIDTH>, SynthesisError> {
    let mut tmp = vec![];
    for (f, s) in first
        .get_tail_state()
        .into_iter()
        .zip(second.get_head_state().into_iter())
    {
        let v = Num::equals(cs, &f, &s)?;
        tmp.push(v);
    }
    // check that length of the final piece is smaller than maximum size
    let (final_len, of) = first.len().add(cs, &second.len())?;
    tmp.push(of.not());
    let valid = smart_and(cs, &tmp)?;
    can_not_be_false_if_flagged(cs, &valid, &execute)?;

    let mut result = FixedWidthEncodingSpongeLikeQueue::<E, I, N, AWIDTH, SWIDTH>::empty();
    result.head_state = first.head_state;
    result.tail_state = second.tail_state;
    result.num_items = final_len;
    result.witness = first.witness;
    result.witness.wit.extend(second.witness.wit);

    Ok(result)
}
