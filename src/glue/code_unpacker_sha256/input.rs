use super::*;

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
pub struct CodeDecommittmentFSM<E: Engine> {
    pub sha256_inner_state: [Num<E>; 8], // 8 uint32 words of internal sha256 state
    pub hash_to_compare_against: [Num<E>; 2], // endianess has been taken care of
    pub current_index: UInt32<E>,
    pub current_page: UInt32<E>,
    pub timestamp: UInt32<E>,
    pub num_rounds_left: UInt16<E>,
    pub length_in_bits: UInt32<E>,
    pub state_get_from_queue: Boolean,
    pub state_decommit: Boolean,
    pub finished: Boolean,
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommittmentFSM<E> {
    fn empty() -> Self {
        Self {
            sha256_inner_state: [Num::<E>::zero(); 8], // 8 uint32 words of internal sha256 state
            hash_to_compare_against: [Num::<E>::zero(); 2], // endianess has been taken care of
            current_index: UInt32::<E>::zero(),
            current_page: UInt32::<E>::zero(),
            timestamp: UInt32::<E>::zero(),
            num_rounds_left: UInt16::<E>::zero(),
            length_in_bits: UInt32::<E>::zero(),
            state_get_from_queue: Boolean::constant(false),
            state_decommit: Boolean::constant(false),
            finished: Boolean::constant(false),
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
pub struct CodeDecommitterFSMInputOutput<E: Engine> {
    pub internal_fsm: CodeDecommittmentFSM<E>,
    pub decommittment_requests_queue_state: FullSpongeLikeQueueState<E>,
    pub memory_queue_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommitterFSMInputOutput<E> {
    fn empty() -> Self {
        Self {
            internal_fsm: CircuitEmpty::<E>::empty(),
            decommittment_requests_queue_state: CircuitEmpty::<E>::empty(),
            memory_queue_state: CircuitEmpty::<E>::empty(),
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
pub struct CodeDecommitterInputData<E: Engine> {
    pub memory_queue_initial_state: FullSpongeLikeQueueState<E>,
    pub sorted_requests_queue_initial_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommitterInputData<E> {
    fn empty() -> Self {
        Self {
            memory_queue_initial_state: FullSpongeLikeQueueState::<E>::empty(),
            sorted_requests_queue_initial_state: FullSpongeLikeQueueState::<E>::empty(),
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
pub struct CodeDecommitterOutputData<E: Engine> {
    pub memory_queue_final_state: FullSpongeLikeQueueState<E>,
}

impl<E: Engine> CircuitEmpty<E> for CodeDecommitterOutputData<E> {
    fn empty() -> Self {
        Self {
            memory_queue_final_state: FullSpongeLikeQueueState::<E>::empty(),
        }
    }
}

pub type CodeDecommitterCycleInputOutput<E> = crate::inputs::ClosedFormInput<
    E,
    CodeDecommitterFSMInputOutput<E>,
    CodeDecommitterInputData<E>,
    CodeDecommitterOutputData<E>,
>;
pub type CodeDecommitterCycleInputOutputWitness<E> = crate::inputs::ClosedFormInputWitness<
    E,
    CodeDecommitterFSMInputOutput<E>,
    CodeDecommitterInputData<E>,
    CodeDecommitterOutputData<E>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct CodeDecommitterCircuitInstanceWitness<E: Engine> {
    pub closed_form_input: CodeDecommitterCycleInputOutputWitness<E>,
    #[serde(bound(
        serialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<DecommitQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub sorted_requests_queue_witness:
        FixedWidthEncodingSpongeLikeQueueWitness<E, DecommitQuery<E>, 2, 3>,
    pub code_words: Vec<Vec<BigUint>>,
}
