use super::*;

pub trait CircuitFixedLengthEncodable<E: Engine, const N: usize>: Clone {
    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; N], SynthesisError>;

    fn encoding_witness(&self) -> Option<[E::Fr; N]> {
        unimplemented!("by default it's not called by queue implementations, and is only required in very edge cases");
    }
}

// impl<E: Engine, T, const N: usize> CircuitFixedLengthEncodable<E, N> for T
//     where T: CSPackable<E, N>
// {
//     fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; N], SynthesisError> {
//         self.pack(cs)
//     }
// }
