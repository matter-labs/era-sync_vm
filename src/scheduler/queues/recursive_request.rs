use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug, Copy)]
pub struct RecursiveRequest<E: Engine> {
    pub circuit_type: Byte<E>,
    pub input_commitment: Num<E>,
}

impl<E: Engine> RecursiveRequest<E> {
    pub fn empty() -> Self {
        Self {
            circuit_type: Byte::zero(),
            input_commitment: Num::zero(),
        }
    }

    pub fn allocate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<RecursiveRequestWitness<E>>,
    ) -> Result<Self, SynthesisError> {
        let circuit_type = witness.as_ref().map(|el| el.circuit_type);
        let circuit_type = Byte::<E>::from_u8_witness(cs, circuit_type)?;

        let input_commitment = witness.as_ref().map(|el| el.input_commitment);
        let input_commitment = Num::alloc(cs, input_commitment)?;

        let new = Self {
            circuit_type,
            input_commitment,
        };

        Ok(new)
    }
}

impl<E: Engine> CircuitEq<E> for RecursiveRequest<E> {
    fn eq(&self, other: &Self) -> bool {
        self.circuit_type.eq(&other.circuit_type)
            && self.input_commitment.eq(&other.input_commitment)
    }
}

impl<E: Engine> CircuitSelectable<E> for RecursiveRequest<E> {
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        if a.eq(b) {
            return Ok(a.clone());
        }

        let circuit_type =
            Byte::<E>::conditionally_select(cs, flag, &a.circuit_type, &b.circuit_type)?;
        let input_commitment =
            Num::conditionally_select(cs, flag, &a.input_commitment, &b.input_commitment)?;

        let new = Self {
            circuit_type,
            input_commitment,
        };

        Ok(new)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, Copy, PartialEq(bound = ""), Eq(bound = ""))]
pub struct RecursiveRequestWitness<E: Engine> {
    pub circuit_type: u8,
    pub input_commitment: E::Fr,
}

impl<E: Engine> RecursiveRequestWitness<E> {
    pub fn empty() -> Self {
        Self {
            circuit_type: 0,
            input_commitment: E::Fr::zero(),
        }
    }
}

impl<E: Engine> RecursiveRequest<E> {
    pub fn pack(&self) -> [Num<E>; 2] {
        [self.circuit_type.inner, self.input_commitment]
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, 2> for RecursiveRequest<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        let packed = self.pack();
        Ok(packed)
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 2]> {
        let circuit_type = self.circuit_type.get_byte_value();
        let input_commitment = self.input_commitment.get_value();

        match (circuit_type, input_commitment) {
            (Some(circuit_type), Some(input_commitment)) => {
                Some([u64_to_fe::<E::Fr>(circuit_type as u64), input_commitment])
            }
            _ => None,
        }
    }
}

impl<E: Engine> CSWitnessable<E> for RecursiveRequest<E> {
    type Witness = RecursiveRequestWitness<E>;

    fn create_witness(&self) -> Option<Self::Witness> {
        let circuit_type = self.circuit_type.get_byte_value();
        let input_commitment = self.input_commitment.get_value();

        match (circuit_type, input_commitment) {
            (Some(circuit_type), Some(input_commitment)) => {
                let wit = RecursiveRequestWitness {
                    circuit_type,
                    input_commitment,
                };

                Some(wit)
            }
            _ => None,
        }
    }

    fn placeholder_witness() -> Self::Witness {
        RecursiveRequestWitness::empty()
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 2> for RecursiveRequest<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 2> for RecursiveRequest<E> {
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 2],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 2>>::encode(&new, cs)?;

        for (enc, val) in encoding.iter().zip(values.iter()) {
            enc.enforce_equal(cs, val)?;
        }

        Ok(new)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 2],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 2>>::encode(&new, cs)?;

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
