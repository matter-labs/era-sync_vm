use super::inscribe_default_range_table_for_bit_width_over_first_three_columns;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::data_structures::alg_binary_tree::rescue_impl::StaticGenericBinaryTreeHasher;
use crate::data_structures::alg_binary_tree::AlgebraicBinaryTreeInnerHasher;
use crate::data_structures::SmallFixedWidthInteger as Integer;
use crate::ff::*;
pub use crate::pairing::bn256::{Bn256, Fr};
use crate::traits::GenericHasher;
use crate::traits::*;
use crate::utils::{AWIDTH_VALUE, SWIDTH_VALUE};
pub(crate) use rand::{Rng, SeedableRng, XorShiftRng};
use rescue_poseidon::{CustomGate, HashParams, RescueParams};
pub use std::convert::TryInto;

pub fn deterministic_rng() -> XorShiftRng {
    XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654])
}

pub fn create_test_artifacts() -> (
    TrivialAssembly<Bn256, PlonkCsWidth4WithNextStepAndCustomGatesParams, Width4MainGateWithDNext>,
    GenericHasher<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >,
    StaticGenericBinaryTreeHasher<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >,
) {
    let cs = TrivialAssembly::<
        Bn256,
        PlonkCsWidth4WithNextStepAndCustomGatesParams,
        Width4MainGateWithDNext,
    >::new();

    let mut params = crate::utils::bn254_rescue_params();
    params.use_custom_gate(CustomGate::QuinticWidth4);
    let committer = GenericHasher::<
        Bn256,
        RescueParams<_, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >::new_from_params(&params);

    let tree_hasher = StaticGenericBinaryTreeHasher::<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >::new(&params);

    (cs, committer, tree_hasher)
}

use crate::bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;

pub fn create_test_artifacts_with_optimized_gate() -> (
    TrivialAssembly<
        Bn256,
        PlonkCsWidth4WithNextStepAndCustomGatesParams,
        SelectorOptimizedWidth4MainGateWithDNext,
    >,
    GenericHasher<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >,
    StaticGenericBinaryTreeHasher<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >,
) {
    let cs = TrivialAssembly::<
        Bn256,
        PlonkCsWidth4WithNextStepAndCustomGatesParams,
        SelectorOptimizedWidth4MainGateWithDNext,
    >::new();

    let mut params = crate::utils::bn254_rescue_params();
    params.use_custom_gate(CustomGate::QuinticWidth4);
    let committer = GenericHasher::<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >::new_from_params(&params);

    let tree_hasher = StaticGenericBinaryTreeHasher::<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >::new(&params);

    (cs, committer, tree_hasher)
}

pub fn create_test_artifacts_with_optimized_gate_extended() -> (
    ProvingAssembly<
        Bn256,
        PlonkCsWidth4WithNextStepAndCustomGatesParams,
        SelectorOptimizedWidth4MainGateWithDNext,
    >,
    TrivialAssembly<
        Bn256,
        PlonkCsWidth4WithNextStepAndCustomGatesParams,
        SelectorOptimizedWidth4MainGateWithDNext,
    >,
    GenericHasher<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >,
    StaticGenericBinaryTreeHasher<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >,
) {
    let cs1 = ProvingAssembly::<
        Bn256,
        PlonkCsWidth4WithNextStepAndCustomGatesParams,
        SelectorOptimizedWidth4MainGateWithDNext,
    >::new();
    let cs2 = TrivialAssembly::<
        Bn256,
        PlonkCsWidth4WithNextStepAndCustomGatesParams,
        SelectorOptimizedWidth4MainGateWithDNext,
    >::new();

    let mut params = crate::utils::bn254_rescue_params();
    params.use_custom_gate(CustomGate::QuinticWidth4);
    let committer = GenericHasher::<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >::new_from_params(&params);

    let tree_hasher = StaticGenericBinaryTreeHasher::<
        Bn256,
        RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
        AWIDTH_VALUE,
        SWIDTH_VALUE,
    >::new(&params);

    (cs1, cs2, committer, tree_hasher)
}
