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
pub struct CodeDecommittmentsDeduplicatorInputData<E: Engine> {
    pub initial_log_queue_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommittmentsDeduplicatorInputData<E> {
    fn empty() -> Self {
        Self {
            initial_log_queue_state: FullSpongeLikeQueueState::<E>::empty(),
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
    (),
    CodeDecommittmentsDeduplicatorInputData<E>,
    CodeDecommittmentsDeduplicatorOutputData<E>,
>;
pub type CodeDecommittmentsDeduplicatorInputOutputWitness<E> =
    crate::inputs::ClosedFormInputWitness<
        E,
        (),
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
    pub intermediate_sorted_queue_state: FullSpongeLikeQueueStateWitness<E>,
    #[serde(bound(
        serialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub sorted_queue_witness: FixedWidthEncodingSpongeLikeQueueWitness<E, DecommitQuery<E>, 2, 3>,
}
