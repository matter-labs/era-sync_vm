use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct PubdataChunk<E: Engine, const S: usize> {
    pub inner: [Byte<E>; S],
}

impl<E: Engine, const S: usize> Copy for PubdataChunk<E, S> {}

impl<E: Engine, const S: usize> PubdataChunk<E, S> {
    pub fn empty() -> Self {
        Self {
            inner: [Byte::zero(); S],
        }
    }

    pub fn allocate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<PubdataChunkWitness<S>>,
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::empty();
        for (i, r) in new.inner.iter_mut().enumerate() {
            let byte = witness.as_ref().map(|el| el.inner[i]);
            *r = Byte::from_u8_witness(cs, byte)?;
        }

        Ok(new)
    }
}

impl<E: Engine, const S: usize> CircuitEq<E> for PubdataChunk<E, S> {
    fn eq(&self, other: &Self) -> bool {
        self.inner
            .iter()
            .zip(other.inner.iter())
            .all(|(a, b)| a.eq(b))
    }
}

impl<E: Engine, const S: usize> CircuitSelectable<E> for PubdataChunk<E, S> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        if a.eq(b) {
            return Ok(a.clone());
        }
        let mut new = Self::empty();
        for ((a, b), r) in a.inner.iter().zip(b.inner.iter()).zip(new.inner.iter_mut()) {
            *r = Byte::conditionally_select(cs, flag, &a, &b)?;
        }

        Ok(new)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq(bound = ""), Eq(bound = ""))]
pub struct PubdataChunkWitness<const S: usize> {
    pub inner: [u8; S],
}

impl<const S: usize> PubdataChunkWitness<S> {
    pub fn empty() -> Self {
        Self { inner: [0u8; S] }
    }
}

impl<E: Engine, const S: usize> PubdataChunk<E, S> {
    pub fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        assert!(S <= (E::Fr::CAPACITY / 8) as usize);

        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::zero();
        for i in 0..S {
            lc.add_assign_number_with_coeff(&self.inner[i].inner, shifts[i * 8]);
        }

        let el = lc.into_num(cs)?;

        Ok(el)
    }
}

impl<E: Engine, const S: usize> CircuitFixedLengthEncodable<E, 1> for PubdataChunk<E, S> {
    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        assert!(S <= (E::Fr::CAPACITY / 8) as usize);

        let packed = self.pack(cs)?;
        Ok([packed])
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 1]> {
        assert!(S <= (E::Fr::CAPACITY / 8) as usize);

        let mut encoding = BigUint::from(0u64);
        for (i, b) in self.inner.iter().enumerate() {
            if let Some(b) = b.get_byte_value() {
                encoding += BigUint::from(b as u64) << (i * 8);
            } else {
                return None;
            }
        }

        let encoding = biguint_to_fe(encoding);

        Some([encoding])
    }
}

impl<E: Engine, const S: usize> CSWitnessable<E> for PubdataChunk<E, S> {
    type Witness = PubdataChunkWitness<S>;

    fn create_witness(&self) -> Option<Self::Witness> {
        assert!(S <= (E::Fr::CAPACITY / 8) as usize);

        let mut wit = PubdataChunkWitness::<S>::empty();

        for (w, b) in wit.inner.iter_mut().zip(self.inner.iter()) {
            if let Some(val) = b.get_byte_value() {
                *w = val;
            } else {
                return None;
            }
        }

        Some(wit)
    }

    fn placeholder_witness() -> Self::Witness {
        assert!(S <= (E::Fr::CAPACITY / 8) as usize);

        PubdataChunkWitness::<S>::empty()
    }
}

impl<E: Engine, const S: usize> CircuitFixedLengthEncodableExt<E, 1> for PubdataChunk<E, S> {}

impl<E: Engine, const S: usize> CircuitFixedLengthDecodableExt<E, 1> for PubdataChunk<E, S> {
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert!(S <= (E::Fr::CAPACITY / 8) as usize);

        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 1>>::encode(&new, cs)?;

        for (enc, val) in encoding.iter().zip(values.iter()) {
            enc.enforce_equal(cs, val)?;
        }

        Ok(new)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 1],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        assert!(S <= (E::Fr::CAPACITY / 8) as usize);

        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 1>>::encode(&new, cs)?;

        let mut tmp = vec![];

        for (enc, val) in encoding.iter().zip(values.iter()) {
            let eq = Num::equals(cs, &enc, val)?;
            tmp.push(eq);
        }

        let eq = smart_and(cs, &tmp)?;
        can_not_be_false_if_flagged(cs, &eq, should_execute)?;

        Ok(new)
    }
}
