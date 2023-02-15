use super::*;

pub const RAM_PERMUTATION_NUM_CHALLENGES: usize = 3;

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
pub struct RamPermutationFSMInputOutput<E: Engine> {
    pub lhs_accumulator: Num<E>,
    pub rhs_accumulator: Num<E>,
    pub current_unsorted_queue_state: FullSpongeLikeQueueState<E>,
    pub current_sorted_queue_state: FullSpongeLikeQueueState<E>,
    pub previous_sorting_key: Num<E>,
    pub previous_full_key: Num<E>,
    pub previous_values_pair: [Num<E>; 2],
    pub previous_is_ptr: Boolean,
    pub num_nondeterministic_writes: UInt32<E>,
}

impl<E: Engine> CircuitEmpty<E> for RamPermutationFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            lhs_accumulator: CircuitEmpty::<E>::empty(),
            rhs_accumulator: CircuitEmpty::<E>::empty(),
            current_unsorted_queue_state: CircuitEmpty::<E>::empty(),
            current_sorted_queue_state: CircuitEmpty::<E>::empty(),
            previous_sorting_key: CircuitEmpty::<E>::empty(),
            previous_full_key: CircuitEmpty::<E>::empty(),
            previous_values_pair: [CircuitEmpty::<E>::empty(); 2],
            previous_is_ptr: CircuitEmpty::<E>::empty(),
            num_nondeterministic_writes: CircuitEmpty::<E>::empty(),
        }
    }
}

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
pub struct RamPermutationInputData<E: Engine> {
    pub unsorted_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub sorted_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub non_deterministic_bootloader_memory_snapshot_length: UInt32<E>,
}

impl<E: Engine> CircuitEmpty<E> for RamPermutationInputData<E> {
    fn empty() -> Self {
        Self {
            unsorted_queue_initial_state: FullSpongeLikeQueueState::<E>::empty(),
            sorted_queue_initial_state: FullSpongeLikeQueueState::<E>::empty(),
            non_deterministic_bootloader_memory_snapshot_length: UInt32::<E>::zero(),
        }
    }
}

pub type RamPermutationCycleInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    RamPermutationFSMInputOutput<E>,
    RamPermutationInputData<E>,
    (),
>;
pub type RamPermutationCycleInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    RamPermutationFSMInputOutput<E>,
    RamPermutationInputData<E>,
    (),
>;
