use super::*;
use cs_derive::*;

use crate::glue::traits::*;
use crate::scheduler::queues::*;

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
)]
#[derivative(Clone, Debug)]
pub struct MemoryArgumentStructuredInput<E: Engine> {
    pub original_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub sorted_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub lhs_accumulator: Num<E>,
    pub rhs_accumulator: Num<E>,
    pub fs_challenges: [Num<E>; 3],
    pub result_lhs_accumulator: Num<E>,
    pub result_rhs_accumulator: Num<E>,
    pub last_element_sorting_key: Num<E>,
    pub last_element_full_key: Num<E>,
    pub last_element_values: [Num<E>; 2],
    pub result_last_element_sorting_key: Num<E>,
    pub result_last_element_full_key: Num<E>,
    pub result_last_element_values: [Num<E>; 2],
    pub continue_argument: Boolean,
    pub continue_further: Boolean,
}
