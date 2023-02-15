use super::*;
use cs_derive::*;

// some queue to save an inner state of sponge like queue

// #[derive(Derivative, NEWCSWitness, NEWCSGetWitness, NEWCSAlloc, NEWCSEqual, NEWCSSelectable, NEWCSPack, NEWFixedLengthEncodableExt, NEWFixedLengthDecodableExt)]
// // #[derive(Derivative, CSAlloc, CSWitness, CSGetWitness, CSEqual, CSSelectable, FixedLengthEncodableExt, FixedLengthDecodableExt)]
// // #[EncodingLength = "11"]
// // #[PackWithCS = "true"]
// #[derivative(Clone, Debug)]

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct SpongeLikeQueueState<E: Engine, const SWIDTH: usize> {
    pub length: UInt32<E>,
    pub sponge_state: [Num<E>; SWIDTH],
}

impl<E: Engine, const SWIDTH: usize> Copy for SpongeLikeQueueState<E, SWIDTH> {}

impl<E: Engine, const SWIDTH: usize> SpongeLikeQueueState<E, SWIDTH> {
    pub fn empty() -> Self {
        Self {
            length: UInt32::zero(),
            sponge_state: [Num::zero(); SWIDTH],
        }
    }

    pub fn allocate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<SpongeLikeQueueStateWitness<E, SWIDTH>>,
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::empty();
        for (i, r) in new.sponge_state.iter_mut().enumerate() {
            let wit = witness.as_ref().map(|el| el.sponge_state[i]);
            *r = Num::alloc(cs, wit)?;
        }
        let length = witness.map(|el| el.length);
        let length = UInt32::allocate(cs, length)?;
        new.length = length;

        Ok(new)
    }

    pub fn equals<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        first: &Self,
        second: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let mut tmp = vec![];
        let e = UInt32::equals(cs, &first.length, &second.length)?;
        tmp.push(e);
        for (f, s) in first.sponge_state.iter().zip(second.sponge_state.iter()) {
            let e = Num::equals(cs, &f, &s)?;
            tmp.push(e);
        }

        smart_and(cs, &tmp)
    }

    pub fn get_witness(&self) -> Option<SpongeLikeQueueStateWitness<E, SWIDTH>> {
        let mut wit = SpongeLikeQueueStateWitness::<E, SWIDTH>::empty();

        if let Some(w) = self.length.get_value() {
            wit.length = w;
        } else {
            return None;
        }

        for (w, b) in wit.sponge_state.iter_mut().zip(self.sponge_state.iter()) {
            if let Some(val) = b.get_value() {
                *w = val;
            } else {
                return None;
            }
        }

        Some(wit)
    }
}

impl<E: Engine, const SWIDTH: usize> CircuitEq<E> for SpongeLikeQueueState<E, SWIDTH> {
    fn eq(&self, other: &Self) -> bool {
        self.sponge_state
            .iter()
            .zip(other.sponge_state.iter())
            .all(|(a, b)| a.eq(b))
            && self.length.eq(&other.length)
    }
}

impl<E: Engine, const SWIDTH: usize> CircuitSelectable<E> for SpongeLikeQueueState<E, SWIDTH> {
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
        for ((a, b), r) in a
            .sponge_state
            .iter()
            .zip(b.sponge_state.iter())
            .zip(new.sponge_state.iter_mut())
        {
            *r = Num::conditionally_select(cs, flag, &a, &b)?;
        }
        new.length = UInt32::conditionally_select(cs, flag, &a.length, &b.length)?;

        Ok(new)
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Copy, PartialEq(bound = ""), Eq(bound = ""))]
pub struct SpongeLikeQueueStateWitness<E: Engine, const SWIDTH: usize> {
    pub length: u32,
    #[serde(bound(serialize = "[E::Fr; SWIDTH]: serde::Serialize"))]
    #[serde(bound(deserialize = "[E::Fr; SWIDTH]: serde::de::DeserializeOwned"))]
    pub sponge_state: [E::Fr; SWIDTH],
}

impl<E: Engine, const SWIDTH: usize> SpongeLikeQueueStateWitness<E, SWIDTH> {
    pub fn empty() -> Self {
        Self {
            length: 0u32,
            sponge_state: [E::Fr::zero(); SWIDTH],
        }
    }
}

impl<E: Engine> SpongeLikeQueueState<E, 3> {
    pub fn pack(&self) -> [Num<E>; 4] {
        [
            self.length.inner,
            self.sponge_state[0],
            self.sponge_state[1],
            self.sponge_state[2],
        ]
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, 4> for SpongeLikeQueueState<E, 3> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 4], SynthesisError> {
        let packed = self.pack();
        Ok(packed)
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 4]> {
        let packed = self.pack();
        Num::get_value_multiple(&packed)
    }
}

impl<E: Engine> CSWitnessable<E> for SpongeLikeQueueState<E, 3> {
    type Witness = SpongeLikeQueueStateWitness<E, 3>;

    fn create_witness(&self) -> Option<Self::Witness> {
        self.get_witness()
    }

    fn placeholder_witness() -> Self::Witness {
        SpongeLikeQueueStateWitness::<E, 3>::empty()
    }
}

impl<E: Engine> CSAllocatable<E> for SpongeLikeQueueState<E, 3> {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::allocate(cs, witness)
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 4> for SpongeLikeQueueState<E, 3> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 4> for SpongeLikeQueueState<E, 3> {
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 4],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 4>>::encode(&new, cs)?;

        for (enc, val) in encoding.iter().zip(values.iter()) {
            enc.enforce_equal(cs, val)?;
        }

        Ok(new)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 4],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let new = Self::allocate(cs, witness)?;
        let encoding = <Self as CircuitFixedLengthEncodable<E, 4>>::encode(&new, cs)?;

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

// quick and dirty composition

const COMPOSITION_WIDTH: usize = 2;

impl<E: Engine> CircuitFixedLengthEncodable<E, { 4 * COMPOSITION_WIDTH }>
    for [SpongeLikeQueueState<E, 3>; COMPOSITION_WIDTH]
{
    fn encode<CS: ConstraintSystem<E>>(
        &self,
        _cs: &mut CS,
    ) -> Result<[Num<E>; 4 * COMPOSITION_WIDTH], SynthesisError> {
        let mut packed = [Num::<E>::zero(); 4 * COMPOSITION_WIDTH];
        for (c, el) in packed.chunks_mut(4).zip(self.iter()) {
            let tmp = el.pack();
            c.copy_from_slice(&tmp);
        }

        Ok(packed)
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 4 * COMPOSITION_WIDTH]> {
        let mut packed = [Num::<E>::zero(); 4 * COMPOSITION_WIDTH];
        for (c, el) in packed.chunks_mut(4).zip(self.iter()) {
            let tmp = el.pack();
            c.copy_from_slice(&tmp);
        }

        Num::get_value_multiple(&packed)
    }
}

// impl<E: Engine> CSWitnessable<E> for [SpongeLikeQueueState<E, 3>; COMPOSITION_WIDTH] {
//     type Witness = [SpongeLikeQueueStateWitness<E, 3>; COMPOSITION_WIDTH];

//     fn create_witness(&self) -> Option<Self::Witness> {
//         let mut wit = [SpongeLikeQueueStateWitness::<E, 3>::empty(); COMPOSITION_WIDTH];

//         for (w, el) in wit.iter_mut().zip(self.iter()) {
//             if let Some(t) = el.create_witness() {
//                 *w = t;
//             } else {
//                 return None
//             }
//         }

//         Some(wit)
//     }

//     fn placeholder_witness() -> Self::Witness {
//         [SpongeLikeQueueStateWitness::<E, 3>::empty(); COMPOSITION_WIDTH]
//     }
// }

impl<E: Engine> CircuitFixedLengthEncodableExt<E, { 4 * COMPOSITION_WIDTH }>
    for [SpongeLikeQueueState<E, 3>; COMPOSITION_WIDTH]
{
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, { 4 * COMPOSITION_WIDTH }>
    for [SpongeLikeQueueState<E, 3>; COMPOSITION_WIDTH]
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let mut result = [SpongeLikeQueueState::<E, 3>::empty(); COMPOSITION_WIDTH];
        for i in 0..COMPOSITION_WIDTH {
            let w = witness.as_ref().map(|el| &el[i]).copied();
            let new = SpongeLikeQueueState::<E, 3>::allocate(cs, w)?;
            result[i] = new;
        }

        Ok(result)
    }
    fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 4 * COMPOSITION_WIDTH],
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let mut result = [SpongeLikeQueueState::<E, 3>::empty(); COMPOSITION_WIDTH];

        for (i, chunk) in values.chunks(4).enumerate() {
            let w = witness.as_ref().map(|el| &el[i]).copied();
            let new = SpongeLikeQueueState::<E, 3>::allocate(cs, w)?;
            let encoding =
                <SpongeLikeQueueState<E, 3> as CircuitFixedLengthEncodable<E, 4>>::encode(
                    &new, cs,
                )?;

            for (enc, val) in encoding.iter().zip(chunk.iter()) {
                enc.enforce_equal(cs, val)?;
            }
            result[i] = new;
        }

        Ok(result)
    }
    fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        values: &[Num<E>; 4 * COMPOSITION_WIDTH],
        should_execute: &Boolean,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let mut result = [SpongeLikeQueueState::<E, 3>::empty(); COMPOSITION_WIDTH];

        let mut tmp = vec![];

        for (i, chunk) in values.chunks(4).enumerate() {
            let w = witness.as_ref().map(|el| &el[i]).copied();
            let new = SpongeLikeQueueState::<E, 3>::allocate(cs, w)?;
            let encoding =
                <SpongeLikeQueueState<E, 3> as CircuitFixedLengthEncodable<E, 4>>::encode(
                    &new, cs,
                )?;

            for (enc, val) in encoding.iter().zip(chunk.iter()) {
                let eq = Num::equals(cs, &enc, val)?;
                tmp.push(eq);
            }
            result[i] = new;
        }

        let eq = smart_and(cs, &tmp)?;
        can_not_be_false_if_flagged(cs, &eq, should_execute)?;

        Ok(result)
    }
}
