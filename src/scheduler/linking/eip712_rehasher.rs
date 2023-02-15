use super::*;
use cs_derive::*;

// everything is encoded already in the queue, so we just need it for input

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct Eip712RehasherStructuredInput<E: Engine> {
    pub queue_head: Num<E>,
    pub queue_tail: Num<E>,
    pub queue_length: UInt32<E>,
}

const ENCODING_LENGTH: usize = 3;

impl<E: Engine> Eip712RehasherStructuredInput<E> {
    pub fn pack(&self) -> [Num<E>; 3] {
        [self.queue_head, self.queue_tail, self.queue_length.inner]
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, ENCODING_LENGTH> for Eip712RehasherStructuredInput<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; ENCODING_LENGTH], SynthesisError> {
        Ok(self.pack())
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, ENCODING_LENGTH> for Eip712RehasherStructuredInput<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, ENCODING_LENGTH> for Eip712RehasherStructuredInput<E> {}
