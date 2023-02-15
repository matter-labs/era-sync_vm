use franklin_crypto::plonk::circuit::hashes_with_tables::tables::BooleanityTable;

use super::*;

pub mod cycle;
pub mod entry_point;
pub mod final_state_merging;
pub mod initial_decoding;
pub mod input;
pub mod memory;
pub mod memory_view;
pub mod opcode_bitmask;
pub mod opcode_execution;
pub mod pre_state;
pub mod witness_oracle;

use zkevm_opcode_defs::REGISTERS_COUNT;

pub fn add_bitwise_8x8_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
) -> Result<(), SynthesisError> {
    use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
    use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;

    let columns3 = vec![
        PolyIdentifier::VariablesPolynomial(0),
        PolyIdentifier::VariablesPolynomial(1),
        PolyIdentifier::VariablesPolynomial(2),
    ];

    use crate::vm::tables::BitwiseLogicTable;

    if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
        let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            BitwiseLogicTable::new(&name, 8),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(bitwise_logic_table)?;
    };

    Ok(())
}

pub fn add_all_tables<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
) -> Result<(), SynthesisError> {
    use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
    use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::tables::ConditionalResolutionTable;
    use crate::vm::tables::NumToBitmaskConverter;
    use crate::vm::tables::OpcodeDecodingTable;
    use crate::vm::tables::ShiftToNumConverter;

    let columns3 = vec![
        PolyIdentifier::VariablesPolynomial(0),
        PolyIdentifier::VariablesPolynomial(1),
        PolyIdentifier::VariablesPolynomial(2),
    ];

    if cs.get_table(VM_SHIFT_TO_NUM_LOW_TABLE_NAME).is_err() {
        let name = VM_SHIFT_TO_NUM_LOW_TABLE_NAME;
        let shift_low_table = LookupTableApplication::new(
            name,
            ShiftToNumConverter::new(&name, true),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(shift_low_table)?;
    };

    if cs.get_table(VM_SHIFT_TO_NUM_HIGH_TABLE_NAME).is_err() {
        let name = VM_SHIFT_TO_NUM_HIGH_TABLE_NAME;
        let shift_high_table = LookupTableApplication::new(
            name,
            ShiftToNumConverter::new(&name, false),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(shift_high_table)?;
    };

    if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
        let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
        let bitwise_logic_table = LookupTableApplication::new(
            name,
            BitwiseLogicTable::new(&name, 8),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(bitwise_logic_table)?;
    };

    if cs.get_table(VM_NUM_TO_BITMASK_TABLE_NAME).is_err() {
        let name = VM_NUM_TO_BITMASK_TABLE_NAME;
        let table = LookupTableApplication::new(
            name,
            NumToBitmaskConverter::new(&name, REGISTERS_COUNT as u64),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(table)?;
    };

    if cs.get_table(VM_SUBPC_TO_BITMASK_TABLE_NAME).is_err() {
        let name = VM_SUBPC_TO_BITMASK_TABLE_NAME;
        let table = LookupTableApplication::new(
            name,
            NumToBitmaskConverter::new(&name, 3 as u64),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(table)?;
    };

    if cs.get_table(VM_CONDITIONAL_RESOLUTION_TABLE_NAME).is_err() {
        let name = VM_CONDITIONAL_RESOLUTION_TABLE_NAME;
        let table = LookupTableApplication::new(
            name,
            ConditionalResolutionTable::new(&name),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(table)?;
    };

    if cs
        .get_table(VM_OPCODE_DECODING_AND_PRICING_TABLE_NAME)
        .is_err()
    {
        let name = VM_OPCODE_DECODING_AND_PRICING_TABLE_NAME;
        let table = LookupTableApplication::new(
            name,
            OpcodeDecodingTable::new(&name),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(table)?;
    };

    if cs
        .get_table(VM_BOOLEAN_BATCH_ALLOCATION_TABLE_NAME)
        .is_err()
    {
        let name = VM_BOOLEAN_BATCH_ALLOCATION_TABLE_NAME;
        let table = LookupTableApplication::new(
            name,
            BooleanityTable::new(&name),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(table)?;
    };

    Ok(())
}

pub fn add_assymmetric_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
) -> Result<(), SynthesisError> {
    // we add a table that will make all lookup T-polys unequal
    use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
    use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
    use crate::vm::tables::BitwiseLogicTable;
    use crate::vm::tables::ConditionalResolutionTable;
    use crate::vm::tables::NumToBitmaskConverter;
    use crate::vm::tables::OpcodeDecodingTable;
    use crate::vm::tables::ShiftToNumConverter;

    let columns3 = vec![
        PolyIdentifier::VariablesPolynomial(0),
        PolyIdentifier::VariablesPolynomial(1),
        PolyIdentifier::VariablesPolynomial(2),
    ];
    if cs.get_table(VM_CONDITIONAL_RESOLUTION_TABLE_NAME).is_err() {
        let name = VM_CONDITIONAL_RESOLUTION_TABLE_NAME;
        let table = LookupTableApplication::new(
            name,
            ConditionalResolutionTable::new(&name),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(table)?;
    };

    if cs
        .get_table(VM_BOOLEAN_BATCH_ALLOCATION_TABLE_NAME)
        .is_err()
    {
        let name = VM_BOOLEAN_BATCH_ALLOCATION_TABLE_NAME;
        let table = LookupTableApplication::new(
            name,
            BooleanityTable::new(&name),
            columns3.clone(),
            None,
            true,
        );
        cs.add_table(table)?;
    };

    Ok(())
}
