use super::*;

use crate::bellman::pairing::ff::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::Engine;
use crate::bellman::SynthesisError;
use crate::utils::log2_floor;
use crate::{bellman::plonk::better_better_cs::cs::*, utils::u64_to_fe};
// use super::opcodes::OpcodeBytes;
use itertools::Itertools;
use num_bigint::BigUint;

pub mod bitshift;
pub mod bitspread;
pub mod bitwise_logic;
pub mod conditional;
pub mod opcodes;

pub use self::bitshift::ShiftToNumConverter;
pub use self::bitspread::NumToBitmaskConverter;
pub use self::bitwise_logic::BitwiseLogicTable;
pub use self::conditional::*;
pub use self::opcodes::OpcodeDecodingTable;
