#![allow(dead_code, unused_imports)]
#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

pub use franklin_crypto;
pub use rescue_poseidon;

use derivative;
use franklin_crypto::bellman;
use franklin_crypto::bellman::pairing;
use franklin_crypto::bellman::pairing::ff;

pub(crate) use self::bellman::plonk::better_better_cs::cs::ConstraintSystem;
pub(crate) use derivative::*;
pub(crate) use franklin_crypto::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;

pub(crate) const VERBOSE_CIRCUITS: bool = false;
// pub(crate) const VERBOSE_CIRCUITS: bool = true;

pub mod circuit_structures;
pub mod data_structures;
pub mod glue;
pub mod inputs;
pub mod precompiles;
pub mod recursion;
pub mod scheduler;
pub mod secp256k1;
pub mod traits;
pub mod utils;
pub mod vm;

#[cfg(any(test, feature = "external_testing"))]
pub mod testing;
