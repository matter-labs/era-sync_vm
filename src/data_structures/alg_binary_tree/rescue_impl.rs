use super::*;
use crate::ff::*;
use crate::pairing::*;
use franklin_crypto::rescue::*;
use rescue_poseidon::{GenericSponge, HashParams};

pub struct StaticGenericBinaryTreeHasher<
    E: Engine,
    P: HashParams<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
> {
    params: P,
    _m: std::marker::PhantomData<E>,
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    StaticGenericBinaryTreeHasher<E, P, AWIDTH, SWIDTH>
{
    pub fn new(params: &P) -> Self {
        assert_eq!(AWIDTH, 2);
        assert_eq!(SWIDTH - AWIDTH, 1);
        Self {
            params: params.clone(),
            _m: std::marker::PhantomData,
        }
    }
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize> Clone
    for StaticGenericBinaryTreeHasher<E, P, AWIDTH, SWIDTH>
{
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
            _m: std::marker::PhantomData,
        }
    }
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    AlgebraicBinaryTreeInnerHasher<E::Fr> for StaticGenericBinaryTreeHasher<E, P, AWIDTH, SWIDTH>
{
    type InOut = E::Fr;

    #[inline]
    fn placeholder_output() -> Self::InOut {
        E::Fr::zero()
    }

    fn node_hash(&self, input: &[Self::InOut; 2], _level: usize) -> Self::InOut {
        let as_vec = GenericSponge::hash(input, &self.params, None);

        as_vec[0]
    }
}
