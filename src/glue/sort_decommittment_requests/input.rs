use super::*;
use cs_derive::*;

use crate::scheduler::queues::FixedWidthEncodingSpongeLikeQueueWitness;

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
pub struct CodeDecommittmentsDeduplicatorFSMInputOutput<E: Engine> {
    pub initial_log_queue_state: FullSpongeLikeQueueState<E>,
    pub sorted_queue_state: FullSpongeLikeQueueState<E>,
    pub final_queue_state: FullSpongeLikeQueueState<E>,

    pub grand_products: [Num<E>; 2],

    pub previous_packed_key: [Num<E>; 2],
    pub previous_item_is_trivial: Boolean,
    pub first_encountered_timestamp: UInt32<E>,
    pub previous_record_encoding: [Num<E>; 2],
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommittmentsDeduplicatorFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            initial_log_queue_state: FullSpongeLikeQueueState::<E>::empty(),
            sorted_queue_state: FullSpongeLikeQueueState::<E>::empty(),
            final_queue_state: FullSpongeLikeQueueState::<E>::empty(),

            grand_products: [Num::<E>::one(); 2],

            previous_packed_key: [Num::<E>::zero(); 2],
            previous_item_is_trivial: Boolean::Constant(true),
            first_encountered_timestamp: UInt32::<E>::empty(),
            previous_record_encoding: [Num::<E>::zero(); 2],
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
pub struct CodeDecommittmentsDeduplicatorInputData<E: Engine> {
    pub initial_log_queue_state: FullSpongeLikeQueueState<E>,
    pub sorted_queue_initial_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommittmentsDeduplicatorInputData<E> {
    fn empty() -> Self {
        Self {
            initial_log_queue_state: FullSpongeLikeQueueState::<E>::empty(),
            sorted_queue_initial_state: FullSpongeLikeQueueState::<E>::empty(),
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
pub struct CodeDecommittmentsDeduplicatorOutputData<E: Engine> {
    pub final_queue_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommittmentsDeduplicatorOutputData<E> {
    fn empty() -> Self {
        Self {
            final_queue_state: FullSpongeLikeQueueState::<E>::empty(),
        }
    }
}

pub type CodeDecommittmentsDeduplicatorInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    CodeDecommittmentsDeduplicatorFSMInputOutput<E>,
    CodeDecommittmentsDeduplicatorInputData<E>,
    CodeDecommittmentsDeduplicatorOutputData<E>,
>;
pub type CodeDecommittmentsDeduplicatorInputOutputWitness<E> =
    crate::inputs::ClosedFormInputWitness<
        E,
        CodeDecommittmentsDeduplicatorFSMInputOutput<E>,
        CodeDecommittmentsDeduplicatorInputData<E>,
        CodeDecommittmentsDeduplicatorOutputData<E>,
    >;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct CodeDecommittmentsDeduplicatorInstanceWitness<E: Engine> {
    pub closed_form_input: CodeDecommittmentsDeduplicatorInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub initial_queue_witness: FixedWidthEncodingSpongeLikeQueueWitness<E, DecommitQuery<E>, 2, 3>,
    #[serde(bound(
        serialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub sorted_queue_witness: FixedWidthEncodingSpongeLikeQueueWitness<E, DecommitQuery<E>, 2, 3>,
    pub previous_record_witness: DecommitQueryWitness<E>,
}
