use super::*;

pub trait CircuitFixedLengthEncodableExt<E: Engine, const N: usize>:
    CircuitFixedLengthEncodable<E, N> + CSWitnessable<E>
{
}

// impl<E: Engine, T: CSWitnessable<E> + CircuitFixedLengthEncodable<E, N>, const N: usize> CircuitFixedLengthEncodableExt<E, N> for T {}
