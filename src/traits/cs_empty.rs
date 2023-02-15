use super::*;

pub trait CircuitEmpty<E: Engine> {
    fn empty() -> Self;
}

impl<E: Engine> CircuitEmpty<E> for () {
    fn empty() -> Self {
        ()
    }
}

impl<E: Engine> CircuitEmpty<E> for Num<E> {
    fn empty() -> Self {
        Num::<E>::zero()
    }
}

impl<E: Engine> CircuitEmpty<E> for Boolean {
    fn empty() -> Self {
        Boolean::constant(false)
    }
}
