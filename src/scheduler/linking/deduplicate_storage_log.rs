use super::*;
use cs_derive::*;

// Takes a raw storage log of a speficic kind and outputs the deduplicated and sorted queue
#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct LogDeduplicationCircuitStructuredInput<E: Engine> {
    pub input_queue_tail: Num<E>,
    pub input_queue_length: UInt32<E>,
    pub log_kind: Byte<E>,
    pub output_queue_tail: Num<E>,
    pub output_queue_length: UInt32<E>,
}

const ENCODING_LENGTH: usize = 5;

impl<E: Engine> LogDeduplicationCircuitStructuredInput<E> {
    pub fn pack(&self) -> [Num<E>; ENCODING_LENGTH] {
        [self.input_queue_tail, self.input_queue_length.inner, self.log_kind.inner, self.output_queue_tail, self.output_queue_length.inner]
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, ENCODING_LENGTH> for LogDeduplicationCircuitStructuredInput<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; ENCODING_LENGTH], SynthesisError> {
        Ok(self.pack())
    }
}

// impl<E: Engine> CSWitnessable<E> for LogDeduplicationCircuitStructuredInput<E> {
//     type Witness = LogDeduplicationCircuitStructuredInputWitness<E>;

//     fn create_witness(&self) -> Option<Self::Witness> {
//         self.get_witness()
//     }

//     fn placeholder_witness() -> Self::Witness {
//         LogDeduplicationCircuitStructuredInputWitness::empty()
//     }
// }

impl<E: Engine> CircuitFixedLengthEncodableExt<E, ENCODING_LENGTH> for LogDeduplicationCircuitStructuredInput<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, ENCODING_LENGTH> for LogDeduplicationCircuitStructuredInput<E> {
    
}
