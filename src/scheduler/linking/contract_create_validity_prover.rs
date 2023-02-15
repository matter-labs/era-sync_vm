use super::*;
use cs_derive::*;

// Any processor that takes a part of the queue and only performs some verification procedure over the arguments
// of the queue
#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct CreateValidityProverStructuredInput<E: Engine> {
    pub create_events_queue_tail: Num<E>,
    pub create_events_queue_length: UInt32<E>,
    pub factory_records_queue_tail: Num<E>,
    pub factory_records_queue_length: UInt32<E>,
}

const ENCODING_LENGTH: usize = 4;

impl<E: Engine> CreateValidityProverStructuredInput<E> {
    pub fn pack(&self) -> [Num<E>; ENCODING_LENGTH] {
        [
            self.create_events_queue_tail, 
            self.create_events_queue_length.inner, 
            self.factory_records_queue_tail,
            self.factory_records_queue_length.inner
        ]
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, ENCODING_LENGTH> for CreateValidityProverStructuredInput<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; ENCODING_LENGTH], SynthesisError> {
        Ok(self.pack())
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, ENCODING_LENGTH> for CreateValidityProverStructuredInput<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, ENCODING_LENGTH> for CreateValidityProverStructuredInput<E> {
    
}
