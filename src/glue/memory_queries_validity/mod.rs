use super::*;
use crate::glue::optimizable_queue::commit_encodable_item;
use crate::glue::optimizable_queue::{
    fixed_width_hash_into_state_using_optimizer, variable_length_hash,
};
use crate::glue::traits::get_vec_witness_raw_with_hint;
use crate::glue::traits::CircuitFixedLengthEncodableExt;
use crate::scheduler::queues::memory_access::*;
use crate::scheduler::queues::*;
use crate::vm::optimizer::sponge_set::SpongeOptimizer;
use crate::vm::primitives::UInt64;

use cs_derive::*;

pub mod input;
// pub mod grand_product;
// pub mod unpack_into_pages;
// pub mod unpack_code_into_executable_pages;
// pub mod unpack_input_into_parent_pages;
pub mod ram_permutation_inout;

// pub mod memory_validity_entry_point;
// pub mod decommit_into_page;
// pub mod decommit_into_page_entry_point;
// pub mod prove_unique_decommitment_requests;
// pub mod prove_unique_decommitments_entry_point;

// pub use memory_validity_entry_point::*;
// pub use decommit_into_page::*;
// pub use decommit_into_page_entry_point::*;
// pub use prove_unique_decommitments_entry_point::*;

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
pub struct ContinuousPermutationArgumentStateInput<E: Engine> {
    pub lhs_accumulator: Num<E>,
    pub rhs_accumulator: Num<E>,
    pub continue_argument: Boolean,
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
)]
#[derivative(Clone, Debug)]
pub struct ContinuousPermutationArgumentStateOutput<E: Engine> {
    pub lhs_accumulator: Num<E>,
    pub rhs_accumulator: Num<E>,
}
