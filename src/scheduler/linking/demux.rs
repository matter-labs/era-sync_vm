use super::*;
use cs_derive::*;

// Takes a raw storage log and performs demultiplexing into storage logs of different kinds

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct LogDemultiplexorStructuredInput<E: Engine> {
    pub input_queue_tail: Num<E>,
    pub input_queue_length: UInt32<E>,
    pub aux_bytes_outputs: [Byte<E>; NUM_SUPPORTED_AUX_BYTES],
    pub queue_tails_outputs: [Num<E>; NUM_SUPPORTED_AUX_BYTES],
    pub queue_lengths_outputs: [UInt32<E>; NUM_SUPPORTED_AUX_BYTES],
}

const ENCODING_LENGTH: usize = 3*NUM_SUPPORTED_AUX_BYTES + 2;

impl<E: Engine> LogDemultiplexorStructuredInput<E> {
    pub fn pack(&self) -> [Num<E>; ENCODING_LENGTH] {
        let mut result = [Num::zero(); ENCODING_LENGTH];
        let mut idx = 0;
        result[idx] = self.input_queue_tail;
        idx += 1;
        result[idx] = self.input_queue_length.inner;
        idx += 1;
        for el in self.aux_bytes_outputs.iter() {
            result[idx] = el.inner;
            idx += 1;
        }
        for el in self.queue_tails_outputs.iter() {
            result[idx] = *el;
            idx += 1;
        }
        for el in self.queue_lengths_outputs.iter() {
            result[idx] = el.inner;
            idx += 1;
        }
        assert_eq!(idx, ENCODING_LENGTH);
        
        result
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, ENCODING_LENGTH> for LogDemultiplexorStructuredInput<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<[Num<E>; ENCODING_LENGTH], SynthesisError> {
        Ok(self.pack())
    }
}

// impl<E: Engine> CSWitnessable<E> for LogDemultiplexorStructuredInput<E> {
//     type Witness = LogDemultiplexorStructuredInputWitness<E>;

//     fn create_witness(&self) -> Option<Self::Witness> {
//         self.get_witness()
//     }

//     fn placeholder_witness() -> Self::Witness {
//         LogDemultiplexorStructuredInputWitness::empty()
//     }
// }

impl<E: Engine> CircuitFixedLengthEncodableExt<E, ENCODING_LENGTH> for LogDemultiplexorStructuredInput<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, ENCODING_LENGTH> for LogDemultiplexorStructuredInput<E> {
    
}
