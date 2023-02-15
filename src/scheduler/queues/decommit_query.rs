use super::*;
use crate::glue::traits::*;
use crate::traits::*;
use crate::vm::primitives::*;
use cs_derive::*;
use franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::DEFAULT_FIRST_BASE_NUM_OF_CHUNKS;
use num_traits::Zero;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct Selector<A, B> {
    select_left: bool,
    left: A,
    right: B,
}

impl<E: Engine, A, B> CSWitnessable<E> for Selector<A, B>
where
    A: CSWitnessable<E>,
    B: CSWitnessable<E, Witness = A::Witness>,
{
    type Witness = A::Witness;
    fn create_witness(&self) -> Option<Self::Witness> {
        if self.select_left {
            self.left.create_witness()
        } else {
            self.right.create_witness()
        }
    }
    fn placeholder_witness() -> Self::Witness {
        A::placeholder_witness()
    }
}

impl<E: Engine, A, B> CSAllocatable<E> for Selector<A, B>
where
    A: CSAllocatable<E>,
    B: CSAllocatable<E, Witness = A::Witness> + CircuitEmpty<E>,
{
    fn alloc_from_witness<CS>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        Ok(Self {
            select_left: true,
            left: A::alloc_from_witness(cs, witness)?,
            right: B::empty(),
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub enum DecommitHash<E: Engine> {
    AsU256(UInt256<E>),
    AsU128x2([UInt128<E>; 2]),
}

impl<E: Engine> DecommitHash<E> {
    pub fn as_u256(self) -> UInt256<E> {
        match self {
            DecommitHash::AsU256(el) => el,
            DecommitHash::AsU128x2(_) => panic!("it must be UInt256 internally"),
        }
    }
}

impl<E: Engine> CSWitnessable<E> for DecommitHash<E> {
    type Witness = BigUint;
    fn create_witness(&self) -> Option<Self::Witness> {
        match self {
            DecommitHash::AsU256(as_u256) => as_u256.create_witness(),
            DecommitHash::AsU128x2(as_u128x2) => {
                let mut base = BigUint::from(0u64);
                let mut shift = 0u32;
                let mut is_none = false;
                for chunk in as_u128x2.iter() {
                    if let Some(v) = chunk.get_value() {
                        base += BigUint::from(v) << shift;
                        shift += 128;
                    } else {
                        is_none = true;
                    }
                }

                if is_none {
                    None
                } else {
                    Some(base)
                }
            }
        }
    }

    fn placeholder_witness() -> BigUint {
        BigUint::zero()
    }
}

impl<E: Engine> CSAllocatable<E> for DecommitHash<E> {
    fn alloc_from_witness<CS>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        Ok(DecommitHash::AsU256(UInt256::alloc_from_witness(
            cs, witness,
        )?))
    }
}

impl<E: Engine> DecommitHash<E> {
    pub const CIRCUIT_ENCODING_LEN: usize = 2;
}

impl<E: Engine> CSPackable<E, 2> for DecommitHash<E> {
    fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        let enc = match self {
            DecommitHash::AsU256(as_u256) => {
                let encoding = as_u256.into_u128_pair(cs)?;
                [encoding[0].inner, encoding[1].inner]
            }
            DecommitHash::AsU128x2(as_u128x2) => [as_u128x2[0].inner, as_u128x2[1].inner],
        };

        Ok(enc)
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, 2> for DecommitHash<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        self.pack(cs)
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 2> for DecommitHash<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 2> for DecommitHash<E> {
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        <Self as CSAllocatable<E>>::alloc_from_witness(cs, witness)
    }
}

#[derive(
    Derivative, CSAllocatable, CSWitnessable, FixedLengthEncodableExt, FixedLengthDecodableExt,
)]
#[EncodingLength = "2"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct DecommitQuery<E: Engine> {
    pub root_hash: DecommitHash<E>,
    pub page: UInt32<E>,
    pub is_first: Boolean,
    pub timestamp: UInt32<E>,
}

impl<E: Engine> DecommitQuery<E> {
    pub fn uninitialized() -> Self {
        DecommitQuery {
            root_hash: DecommitHash::AsU256(UInt256::zero()),
            page: UInt32::<E>::zero(),
            is_first: Boolean::constant(false),
            timestamp: UInt32::<E>::zero(),
        }
    }

    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 2], SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        let mut cur_shift = 0;
        lc.add_assign_number_with_coeff(&self.page.inner, E::Fr::one());
        cur_shift += 32;
        match &self.root_hash {
            DecommitHash::AsU256(as_u256) => {
                lc.add_assign_number_with_coeff(&as_u256.inner[0].inner, shifts[cur_shift].clone());
                cur_shift += 64;
                lc.add_assign_number_with_coeff(&as_u256.inner[1].inner, shifts[cur_shift].clone());
                cur_shift += 64;
            }
            DecommitHash::AsU128x2(as_u128x2) => {
                lc.add_assign_number_with_coeff(&as_u128x2[0].inner, shifts[cur_shift].clone());
                cur_shift += 64;
            }
        };
        lc.add_assign_boolean_with_coeff(&self.is_first, shifts[cur_shift].clone());
        let el0 = lc.into_num(cs)?;

        let mut lc = LinearCombination::zero();
        let mut cur_shift = 0;
        match &self.root_hash {
            DecommitHash::AsU256(as_u256) => {
                lc.add_assign_number_with_coeff(&as_u256.inner[2].inner, shifts[cur_shift].clone());
                cur_shift += 64;
                lc.add_assign_number_with_coeff(&as_u256.inner[3].inner, shifts[cur_shift].clone());
                cur_shift += 64;
            }
            DecommitHash::AsU128x2(as_u128x2) => {
                lc.add_assign_number_with_coeff(&as_u128x2[1].inner, shifts[cur_shift].clone());
                cur_shift += 64;
            }
        };
        lc.add_assign_number_with_coeff(&self.timestamp.inner, shifts[cur_shift].clone());
        let el1 = lc.into_num(cs)?;

        Ok([el0, el1])
    }
}

pub type DecommitQueue<E, const AW: usize, const SW: usize> =
    FixedWidthEncodingSpongeLikeQueue<E, DecommitQuery<E>, 2, AW, SW>;

#[test]
fn test_decommit() {
    fn assert_serde<T: serde::Serialize + serde::de::DeserializeOwned>(_: T) -> () {}

    let q = DecommitQuery::<crate::pairing::bn256::Bn256>::placeholder_witness();
    let _ = assert_serde(q);

    let queue = FixedWidthEncodingSpongeLikeQueueWitness::<
        crate::pairing::bn256::Bn256,
        DecommitQuery<_>,
        2,
        3,
    >::empty();
    let _ = assert_serde(queue);
}
