use super::zeroable_point::*;
use super::*;

use franklin_crypto::plonk::circuit::bigint::field::*;

pub fn g1_into_in_field_limbs<E: Engine>(
    g1: E::G1Affine,
    rns_params: &RnsParameters<E, E::Fq>,
) -> (Vec<E::Fr>, Vec<E::Fr>) {
    let (mut x, mut y) = g1.into_xy_unchecked();
    if g1.is_zero() {
        x = E::Fq::zero();
        y = E::Fq::zero();
    }
    let (mut x_binary_limbs, _) = split_into_limbs(x, rns_params);
    let (mut y_binary_limbs, _) = split_into_limbs(y, rns_params);

    x_binary_limbs.truncate(rns_params.num_limbs_for_in_field_representation);
    y_binary_limbs.truncate(rns_params.num_limbs_for_in_field_representation);

    (x_binary_limbs, y_binary_limbs)
}

pub fn some_g1_into_in_field_limbs<E: Engine>(
    g1: Option<E::G1Affine>,
    rns_params: &RnsParameters<E, E::Fq>,
) -> (Vec<Option<E::Fr>>, Vec<Option<E::Fr>>) {
    match g1 {
        Some(g1) => {
            let (x_limbs, y_limbs) = g1_into_in_field_limbs(g1, rns_params);
            let x_limbs: Vec<Option<E::Fr>> = x_limbs.into_iter().map(|el| Some(el)).collect();
            let y_limbs: Vec<Option<E::Fr>> = y_limbs.into_iter().map(|el| Some(el)).collect();

            (x_limbs, y_limbs)
        }
        None => {
            let num_limbs = rns_params.num_limbs_for_in_field_representation;
            (vec![None; num_limbs], vec![None; num_limbs])
        }
    }
}

pub fn write_g1_point<E: Engine>(
    point: E::G1Affine,
    dst: &mut Vec<E::Fr>,
    params: &RnsParameters<E, E::Fq>,
) {
    let (x_limbs, y_limbs) = g1_into_in_field_limbs(point, params);
    dst.extend(x_limbs);
    dst.extend(y_limbs);
}

pub fn write_g1_points_vec<E: Engine>(
    points: &[E::G1Affine],
    dst: &mut Vec<E::Fr>,
    params: &RnsParameters<E, E::Fq>,
) {
    for &p in points.iter() {
        write_g1_point(p, dst, params);
    }
}

#[track_caller]
pub fn take<'a, T>(slice: &mut &'a [T], n: usize) -> &'a [T] {
    assert!(slice.len() >= n);
    let (first, second) = slice.split_at(n);
    *slice = second;

    first
}

#[track_caller]
pub fn allocate_vec_of_bytes_of_some_length<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &Option<Vec<u8>>,
    length: usize,
) -> Result<Vec<Byte<E>>, SynthesisError> {
    if let Some(w) = witness.as_ref() {
        assert_eq!(w.len(), length);
    }
    let mut result = vec![];
    for idx in 0..length {
        let w = witness.as_ref().map(|el| el[idx]);
        let a = Byte::from_u8_witness(cs, w)?;
        result.push(a);
    }

    Ok(result)
}

#[track_caller]
pub fn allocate_fixed_byte_array<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &Option<[u8; 32]>,
) -> Result<Vec<Byte<E>>, SynthesisError> {
    let mut result = vec![];
    for idx in 0..32 {
        let w = witness.as_ref().map(|el| el[idx]);
        let a = Byte::from_u8_witness(cs, w)?;
        result.push(a);
    }

    Ok(result)
}

pub fn allocate_vec_of_booleans<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &[Option<bool>],
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut result = vec![];
    for &w in witness.iter() {
        let a = Boolean::from(AllocatedBit::alloc(cs, w)?);
        result.push(a);
    }

    Ok(result)
}

#[track_caller]
pub fn allocate_vec_of_booleans_of_some_length<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &Option<Vec<bool>>,
    length: usize,
) -> Result<Vec<Boolean>, SynthesisError> {
    if let Some(w) = witness.as_ref() {
        assert_eq!(w.len(), length);
    }
    let mut result = vec![];
    for idx in 0..length {
        let w = witness.as_ref().map(|el| el[idx]);
        let a = Boolean::from(AllocatedBit::alloc(cs, w)?);
        result.push(a);
    }

    Ok(result)
}

pub fn allocate_vec_of_nums<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &[Option<E::Fr>],
) -> Result<Vec<Num<E>>, SynthesisError> {
    let mut result = vec![];
    for w in witness.iter() {
        let a = Num::Variable(AllocatedNum::alloc(cs, || Ok(*w.get()?))?);
        result.push(a);
    }

    Ok(result)
}

#[track_caller]
pub fn allocate_vec_of_nums_of_some_length<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &Option<Vec<E::Fr>>,
    length: usize,
) -> Result<Vec<Num<E>>, SynthesisError> {
    if let Some(w) = witness.as_ref() {
        assert_eq!(w.len(), length);
    }
    let mut result = vec![];
    for idx in 0..length {
        let w = witness.as_ref().map(|el| el[idx]);
        let a = Num::Variable(AllocatedNum::alloc(cs, || Ok(*w.get()?))?);
        result.push(a);
    }

    Ok(result)
}

pub fn allocate_vec_of_g1s<'a, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &[Num<E>],
    rns_params: &'a RnsParameters<E, E::Fq>,
) -> Result<Vec<PointAffine<'a, E, E::G1Affine>>, SynthesisError> {
    let chunk_per_point = rns_params.num_limbs_for_in_field_representation * 2;
    assert!(witness.len() % chunk_per_point == 0);
    let mut result = vec![];

    for w in witness.chunks_exact(chunk_per_point) {
        let p = allocate_g1_from_witness(cs, w, rns_params)?;
        result.push(p);
    }

    Ok(result)
}

pub fn allocate_g1_from_witness<'a, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    witness: &[Num<E>],
    rns_params: &'a RnsParameters<E, E::Fq>,
) -> Result<PointAffine<'a, E, E::G1Affine>, SynthesisError> {
    let chunk_per_point = rns_params.num_limbs_for_in_field_representation * 2;
    assert_eq!(witness.len(), chunk_per_point);

    // let p = PointAffine::allocate_from_in_field_binary_limbs_non_zero(
    //     cs,
    //     witness,
    //     rns_params
    // )?;

    let p = PointAffine::allocate_from_in_field_binary_limbs(cs, witness, rns_params)?;

    Ok(p)
}

pub(crate) fn encode_affine_point<'a, E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    point: AffinePoint<'a, E, E::G1Affine>,
) -> Result<Vec<Num<E>>, SynthesisError> {
    let x = point
        .x
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;
    let y = point
        .y
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;

    let params = x.representation_params;
    let num_limbs_in_field = params.num_limbs_for_in_field_representation;

    let mut encoding = vec![];

    for coord in [x, y].iter() {
        for limb in coord.binary_limbs[0..num_limbs_in_field].iter() {
            let as_num = limb.term.into_num();
            encoding.push(as_num);
        }
    }

    Ok(encoding)
}
