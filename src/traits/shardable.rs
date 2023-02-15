use super::*;
use crate::franklin_crypto::plonk::circuit::byte::Byte;

pub trait Shardable<E: Engine> {
    fn shard_id(&self) -> Byte<E>;
}
