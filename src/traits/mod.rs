use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;

use crate::derivative::*;
use rescue_poseidon::{GenericSponge, HashParams};

use super::ConstraintSystem;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::Assignment;

pub mod addressable;
pub mod cs_allocatable;
pub mod cs_decodable_ext;
pub mod cs_empty;
pub mod cs_encodable;
pub mod cs_encodable_ext;
pub mod cs_packable;
pub mod cs_variable_length;
pub mod cs_witnessable;
pub mod shardable;

pub use self::addressable::*;
pub use self::cs_allocatable::*;
pub use self::cs_decodable_ext::*;
pub use self::cs_empty::*;
pub use self::cs_encodable::*;
pub use self::cs_encodable_ext::*;
pub use self::cs_packable::*;
pub use self::cs_variable_length::*;
pub use self::cs_witnessable::*;
pub use self::shardable::*;

pub trait ArithmeticEncodable<E: Engine>: Clone + Send + Sync {
    fn encoding_length_is_constant() -> bool {
        true
    }
    fn encoding_length() -> usize;
    fn encode(&self) -> Result<Vec<E::Fr>, SynthesisError>;
    fn encoding_length_for_instance(&self) -> usize {
        if Self::encoding_length_is_constant() {
            Self::encoding_length()
        } else {
            unimplemented!()
        }
    }
}

pub trait ArithmeticDecodable<E: Engine>: Clone + Send + Sync {
    fn parse(values: &[E::Fr]) -> Result<Self, SynthesisError>;
}

pub trait FixedLengthEncodable<E: Engine, const N: usize>: Clone + std::fmt::Debug {
    fn encode(&self) -> [E::Fr; N];
    fn placeholder() -> Self;
}

pub trait FixedLengthDecodable<E: Engine, const N: usize>: Clone + Send + Sync {
    fn parse(values: &[E::Fr; N]) -> Self;
    fn parse_conditionally(values: &[E::Fr; N], should_execute: bool) -> Self;
}

pub trait ArithmeticCommitter<E: Engine>: Clone + Send + Sync {
    fn commit(&self, values: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError>;
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct GenericHasher<
    E: Engine,
    P: HashParams<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
> {
    pub(crate) params: P,
    #[serde(skip)]
    _m: std::marker::PhantomData<E>,
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    std::cmp::PartialEq for GenericHasher<E, P, AWIDTH, SWIDTH>
{
    fn eq(&self, other: &Self) -> bool {
        self.params.hash_family() == other.params.hash_family()
    }
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    std::cmp::Eq for GenericHasher<E, P, AWIDTH, SWIDTH>
{
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    GenericHasher<E, P, AWIDTH, SWIDTH>
{
    pub fn new_from_params(params: &P) -> Self {
        Self {
            params: params.clone(),
            _m: std::marker::PhantomData,
        }
    }
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    ArithmeticCommitter<E> for GenericHasher<E, P, AWIDTH, SWIDTH>
{
    fn commit(&self, values: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        let output = GenericSponge::hash(values, &self.params, None).to_vec();

        Ok(output)
    }
}

pub trait ArithmeticCommitable<E: Engine>: ArithmeticEncodable<E> {
    fn commit<C: ArithmeticCommitter<E>>(&self, committer: &C) -> Result<E::Fr, SynthesisError> {
        let encoding = self.encode()?;
        let result = committer.commit(&encoding)?;

        Ok(result[0])
    }
}
