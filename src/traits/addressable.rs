use super::*;
use crate::vm::primitives::*;

pub trait Addressable<E: Engine> {
    fn bound_address(&self) -> UInt160<E>;
}
