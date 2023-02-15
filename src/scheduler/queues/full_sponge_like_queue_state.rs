use super::*;

// some queue to save an inner state of sponge like queue, capturing head too
#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
)]
#[derivative(Clone, Debug)]
pub struct FullSpongeLikeQueueState<E: Engine> {
    pub length: UInt32<E>,
    pub head: [Num<E>; 3],
    pub tail: [Num<E>; 3],
}

impl<E: Engine> Copy for FullSpongeLikeQueueState<E> {}

impl<E: Engine> CircuitEmpty<E> for FullSpongeLikeQueueState<E> {
    fn empty() -> Self {
        Self {
            length: UInt32::zero(),
            head: [Num::zero(); 3],
            tail: [Num::zero(); 3],
        }
    }
}

impl<E: Engine> FullSpongeLikeQueueState<E> {
    pub fn take_state<
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
    >(
        queue: &FixedWidthEncodingSpongeLikeQueue<E, I, N, 2, 3>,
    ) -> Self {
        Self {
            length: queue.len(),
            head: queue.get_head_state(),
            tail: queue.get_tail_state(),
        }
    }
}
