use super::*;

// some queue to save an inner state of sponge like queue

#[derive(Derivative, CSAllocatable, CSWitnessable, CSPackable)]
#[derivative(Clone, Debug)]
pub struct QueueState<E: Engine> {
    pub length: UInt32<E>,
    pub state: Num<E>,
}

impl<E: Engine> Copy for QueueState<E> {}

impl<E: Engine> QueueState<E> {
    pub fn empty() -> Self {
        Self {
            length: UInt32::zero(),
            state: Num::zero(),
        }
    }

    pub fn allocate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<QueueStateWitness<E>>,
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::empty();
        let state = witness.as_ref().map(|el| el.state);
        new.state = Num::alloc(cs, state)?;

        let length = witness.map(|el| el.length);
        let length = UInt32::allocate(cs, length)?;
        new.length = length;

        Ok(new)
    }
}

impl<E: Engine> CircuitEq<E> for QueueState<E> {
    fn eq(&self, other: &Self) -> bool {
        self.state.eq(&other.state) && self.length.eq(&other.length)
    }
}

impl<E: Engine> CircuitSelectable<E> for QueueState<E> {
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
        new.state = Num::conditionally_select(cs, flag, &a.state, &b.state)?;
        new.length = UInt32::conditionally_select(cs, flag, &a.length, &b.length)?;

        Ok(new)
    }
}

// #[derive(Derivative)]
// #[derivative(Clone, Debug)]
// pub struct QueueStateWitness<E: Engine> {
//     pub length: u32,
//     pub state: E::Fr,
// }

impl<E: Engine> QueueStateWitness<E> {
    pub fn empty() -> Self {
        Self {
            length: 0u32,
            state: E::Fr::zero(),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E: Engine> QueueState<E> {
    pub fn pack(&self) -> [Num<E>; 2] {
        [self.length.inner, self.state]
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, 2> for QueueState<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; 2], SynthesisError> {
        let packed = self.pack();
        Ok(packed)
    }

    fn encoding_witness(&self) -> Option<[E::Fr; 2]> {
        let packed = self.pack();
        Num::get_value_multiple(&packed)
    }
}

// impl<E: Engine> CSWitnessable<E> for QueueState<E> {
//     type Witness = QueueStateWitness<E>;

//     fn create_witness(&self) -> Option<Self::Witness> {
//         let mut wit = QueueStateWitness::<E>::empty();

//         if let Some(w) = self.length.get_value() {
//             wit.length = w;
//         } else {
//             return None;
//         }

//         if let Some(w) = self.state.get_value() {
//             wit.state = w;
//         } else {
//             return None;
//         }

//         Some(wit)
//     }

//     fn placeholder_witness() -> Self::Witness {
//         QueueStateWitness::<E>::empty()
//     }
// }

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 2> for QueueState<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 2> for QueueState<E> {
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

#[derive(
    Derivative,
    CSWitnessable,
    CSAllocatable,
    CSEqual,
    CSSelectable,
    CSPackable,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct FixedWidthEncodingGenericQueueState<E: Engine> {
    pub num_items: UInt32<E>,
    pub head_state: Num<E>,
    pub tail_state: Num<E>,
}

impl<E: Engine> Copy for FixedWidthEncodingGenericQueueState<E> {}

impl<E: Engine> CircuitEmpty<E> for FixedWidthEncodingGenericQueueState<E> {
    fn empty() -> Self {
        Self {
            num_items: UInt32::zero(),
            head_state: Num::zero(),
            tail_state: Num::zero(),
        }
    }
}

impl<E: Engine> FixedWidthEncodingGenericQueueState<E> {
    pub fn take_state<
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
    >(
        queue: &FixedWidthEncodingGenericQueue<E, I, N>,
    ) -> Self {
        Self {
            num_items: queue.len(),
            head_state: queue.get_head_state(),
            tail_state: queue.get_tail_state(),
        }
    }
}
