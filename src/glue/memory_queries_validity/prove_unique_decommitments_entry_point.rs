use super::*;
use cs_derive::*;

use crate::glue::traits::*;
use crate::scheduler::queues::*;

#[derive(Derivative, CSAllocatable, CSWitnessable, CSPackable, CSSelectable, CSEqual, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct SortAndDepuplicateDecommitmentsStructuredInput<E: Engine> {
    pub unsorted_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub unsorted_queue_final_state: FullSpongeLikeQueueState<E>,
    pub sorted_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub sorted_queue_final_state: FullSpongeLikeQueueState<E>,
    pub result_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub result_queue_final_state: FullSpongeLikeQueueState<E>,
    pub fs_challenges: [Num<E>; 3],
    pub input_state: ContinuousPermutationArgumentStateInput<E>,
    pub output_state: ContinuousPermutationArgumentStateOutput<E>,
    pub input_kv: SortAndDepuplicateDecommitmentsKeyValueSet<E>,
    pub output_kv: SortAndDepuplicateDecommitmentsKeyValueSet<E>,
}

#[derive(Derivative, CSAllocatable, CSWitnessable, CSPackable, CSSelectable, CSEqual, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct SortAndDepuplicateDecommitmentsKeyValueSet<E: Engine> {
    pub sorting_key: UInt32<E>,
    pub value: Num<E>,
}