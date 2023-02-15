use super::*;
use cs_derive::*;

// Any processor that takes a part of the queue and only performs some verification procedure over the arguments
// of the queue
#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct QueueProcessorStructuredInput<E: Engine> {
    pub queue_head: Num<E>,
    pub queue_tail: Num<E>,
    pub queue_length: UInt32<E>,
}

const ENCODING_LENGTH: usize = 3;

impl<E: Engine> QueueProcessorStructuredInput<E> {
    pub fn pack(&self) -> [Num<E>; 3] {
        [self.queue_head, self.queue_tail, self.queue_length.inner]
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, ENCODING_LENGTH> for QueueProcessorStructuredInput<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; ENCODING_LENGTH], SynthesisError> {
        Ok(self.pack())
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, ENCODING_LENGTH> for QueueProcessorStructuredInput<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, ENCODING_LENGTH> for QueueProcessorStructuredInput<E> {}
