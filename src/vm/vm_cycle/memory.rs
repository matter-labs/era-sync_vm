use super::*;
use crate::glue::code_unpacker_sha256::memory_query_updated::RawMemoryQueryWitness;
use crate::glue::traits::*;
use crate::vm::primitives::register_view::Register;
use crate::vm::vm_cycle::initial_decoding::OpcodeFinalDecoding;
use crate::vm::vm_cycle::witness_oracle::MemoryWitness;
use cs_derive::*;
use zkevm_opcode_defs::ImmMemHandlerFlags;

#[derive(CSAllocatable, CSWitnessable, Clone)]
pub struct MemoryLocation<E: Engine> {
    pub page: UInt32<E>,
    pub index: UInt32<E>,
}

pub fn resolve_memory_region_and_index_for_source<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    code_page: UInt32<E>,
    stack_page: UInt32<E>,
    register_low_value: UInt16<E>,
    opcode_props: &OpcodeFinalDecoding<E>,
    optimizer: &mut OptimizationContext<E>,
    current_sp: UInt16<E>,
) -> Result<(MemoryLocation<E>, UInt16<E>, Boolean), SynthesisError> {
    // we assume that we did quickly select low part of the register before somehow, so we

    let use_code = opcode_props
        .properties_bits
        .boolean_for_src_mem_access(ImmMemHandlerFlags::UseCodePage);
    let use_stack_absolute = opcode_props
        .properties_bits
        .boolean_for_src_mem_access(ImmMemHandlerFlags::UseAbsoluteOnStack);
    let use_stack_relative = opcode_props
        .properties_bits
        .boolean_for_src_mem_access(ImmMemHandlerFlags::UseStackWithOffset);
    let use_stack_with_push_pop = opcode_props
        .properties_bits
        .boolean_for_src_mem_access(ImmMemHandlerFlags::UseStackWithPushPop);

    let absolute_mode = smart_or(cs, &[use_code, use_stack_absolute])?;
    let (index_for_absolute, _) =
        register_low_value.add_using_delayed_bool_allocation(cs, &opcode_props.imm0, optimizer)?;
    let (index_for_relative, _) =
        current_sp.sub_using_delayed_bool_allocation(cs, &index_for_absolute, optimizer)?;

    // if we use absolute addressing then we just access reg + imm mod 2^16
    // if we use relative addressing then we access sp +/- (reg + imm), and if we push/pop then we update sp to such value

    // here we only read

    // manually unrolled selection. We KNOW that either we will not care about this particular value,
    // or one of the bits here was set anyway

    let use_stack = smart_or(
        cs,
        &[
            use_stack_absolute,
            use_stack_relative,
            use_stack_with_push_pop,
        ],
    )?;
    let did_read = smart_or(cs, &[use_stack, use_code])?;
    // we have a special rule for NOP opcode: if we NOP then even though we CAN formally address the memory we SHOULD NOT read
    let is_nop = opcode_props
        .properties_bits
        .boolean_for_opcode(zkevm_opcode_defs::Opcode::Nop(zkevm_opcode_defs::NopOpcode));
    let did_read = smart_and(cs, &[did_read, is_nop.not()])?;
    let page = UInt32::conditionally_select(cs, &use_stack, &stack_page, &code_page)?;

    let index =
        UInt16::conditionally_select(cs, &absolute_mode, &index_for_absolute, &index_for_relative)?;

    let new_sp = UInt16::conditionally_select(
        cs,
        &use_stack_with_push_pop,
        &index_for_relative,
        &current_sp,
    )?;
    let location = MemoryLocation {
        page,
        index: UInt32::from_num_unchecked(index.inner),
    };

    Ok((location, new_sp, did_read))
}

pub fn resolve_memory_region_and_index_for_dest<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    stack_page: UInt32<E>,
    register_low_value: UInt16<E>,
    opcode_props: &OpcodeFinalDecoding<E>,
    optimizer: &mut OptimizationContext<E>,
    current_sp: UInt16<E>,
) -> Result<(MemoryLocation<E>, UInt16<E>, Boolean), SynthesisError> {
    // we assume that we did quickly select low part of the register before somehow, so we

    let use_stack_absolute = opcode_props
        .properties_bits
        .boolean_for_dst_mem_access(ImmMemHandlerFlags::UseAbsoluteOnStack);
    let use_stack_relative = opcode_props
        .properties_bits
        .boolean_for_dst_mem_access(ImmMemHandlerFlags::UseStackWithOffset);
    let use_stack_with_push_pop = opcode_props
        .properties_bits
        .boolean_for_dst_mem_access(ImmMemHandlerFlags::UseStackWithPushPop);

    let absolute_mode = use_stack_absolute;
    let (index_for_absolute, _) =
        register_low_value.add_using_delayed_bool_allocation(cs, &opcode_props.imm1, optimizer)?;
    let (index_for_relative_with_push, _) =
        current_sp.add_using_delayed_bool_allocation(cs, &index_for_absolute, optimizer)?;
    let (index_for_relative, _) =
        current_sp.sub_using_delayed_bool_allocation(cs, &index_for_absolute, optimizer)?;

    // if we use absolute addressing then we just access reg + imm mod 2^16
    // if we use relative addressing then we access sp +/- (reg + imm), and if we push/pop then we update sp

    // here we only write

    // manually unrolled selection. We KNOW that either we will not care about this particular value,
    // or one of the bits here was set anyway

    let page = stack_page;
    let did_write = smart_or(
        cs,
        &[
            use_stack_absolute,
            use_stack_relative,
            use_stack_with_push_pop,
        ],
    )?;
    // we have a special rule for NOP opcode: if we NOP then even though we CAN formally address the memory we SHOULD NOT write
    let is_nop = opcode_props
        .properties_bits
        .boolean_for_opcode(zkevm_opcode_defs::Opcode::Nop(zkevm_opcode_defs::NopOpcode));
    let did_write = smart_and(cs, &[did_write, is_nop.not()])?;

    let index_with_somewhat_relative_addressing = UInt16::conditionally_select(
        cs,
        &use_stack_with_push_pop,
        &index_for_relative_with_push,
        &index_for_relative,
    )?;

    let index = UInt16::conditionally_select(
        cs,
        &absolute_mode,
        &index_for_absolute,
        &index_with_somewhat_relative_addressing,
    )?;

    let new_sp = UInt16::conditionally_select(
        cs,
        &use_stack_with_push_pop,
        &index_for_relative_with_push,
        &current_sp,
    )?;

    let location = MemoryLocation {
        page,
        index: UInt32::from_num_unchecked(index.inner),
    };

    Ok((location, new_sp, did_write))
}

use crate::vm::vm_cycle::witness_oracle::WitnessOracle;

/// NOTE: final state is one if we INDEED READ, so extra care should be taken to select and preserve markers
/// if we ever need it or not
pub fn may_be_read_memory_for_code<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    should_access: Boolean,
    timestamp: UInt32<E>,
    location: MemoryLocation<E>,
    current_memory_sponge_state: [Num<E>; 3],
    current_memory_sponge_length: UInt32<E>,
    round_function: &R,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<
    (
        [UInt64<E>; 4],
        ([Num<E>; 3], [Num<E>; 3], UInt32<E>, Boolean),
    ),
    SynthesisError,
> {
    use crate::vm::vm_cycle::memory_view::code_view::CodeReadQuery;
    use crate::vm::vm_cycle::memory_view::read_view::MemoryKey;

    // dbg!(timestamp.get_value());
    let witness_value =
        witness_oracle.get_memory_witness_for_read(timestamp, &location, &should_access);

    let MemoryLocation { page, index } = location;
    let memory_key = MemoryKey {
        timestamp,
        memory_page: page,
        memory_index: index,
    };
    let (witness_value, is_ptr) = match witness_value {
        Some(MemoryWitness { value, is_ptr }) => (Some(value), Some(is_ptr)),
        None => (None, None),
    };
    if let Some(wit) = is_ptr {
        assert!(wit == false);
    }
    let read_query = CodeReadQuery::from_key_and_value_witness(cs, memory_key, witness_value)?;

    let raw_query = read_query.into_raw_query(cs)?;

    use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQueriesQueue;
    let (intermediate_states, new_length) =
        MemoryQueriesQueue::push_and_output_states_relation_raw(
            cs,
            &raw_query,
            &should_access,
            current_memory_sponge_state,
            current_memory_sponge_length,
            round_function,
        )?;

    assert_eq!(intermediate_states.len(), 1);

    let (initial_state, final_state) = intermediate_states[0];
    // mask final state if we do not use a sponge, so it can properly continue
    let final_state = <[Num<E>; 3]>::conditionally_select(
        cs,
        &should_access,
        &final_state,
        &current_memory_sponge_state,
    )?;

    let values = [
        read_query.u64_word_0,
        read_query.u64_word_1,
        read_query.u64_word_2,
        read_query.u64_word_3,
    ];

    Ok((
        values,
        (initial_state, final_state, new_length, should_access),
    ))
}

/// NOTE: final state is one if we INDEED READ, so extra care should be taken to select and preserve markers
/// if we ever need it or not
pub fn may_be_read_memory_for_source_operand<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    should_access: Boolean,
    timestamp: UInt32<E>,
    location: MemoryLocation<E>,
    current_memory_sponge_state: [Num<E>; 3],
    current_memory_sponge_length: UInt32<E>,
    round_function: &R,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<(Register<E>, ([Num<E>; 3], [Num<E>; 3], UInt32<E>, Boolean)), SynthesisError> {
    use crate::vm::vm_cycle::memory_view::read_view::MemoryKey;
    use crate::vm::vm_cycle::memory_view::read_view::MemoryReadQuery;

    // dbg!(timestamp.get_value());
    let witness_value =
        witness_oracle.get_memory_witness_for_read(timestamp, &location, &should_access);

    let MemoryLocation { page, index } = location;
    let memory_key = MemoryKey {
        timestamp,
        memory_page: page,
        memory_index: index,
    };
    let read_query = MemoryReadQuery::from_key_and_value_witness(cs, memory_key, witness_value)?;

    let raw_query = read_query.into_raw_query(cs)?;

    use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQueriesQueue;
    let (intermediate_states, new_length) =
        MemoryQueriesQueue::push_and_output_states_relation_raw(
            cs,
            &raw_query,
            &should_access,
            current_memory_sponge_state,
            current_memory_sponge_length,
            round_function,
        )?;

    assert_eq!(intermediate_states.len(), 1);

    let (initial_state, final_state) = intermediate_states[0];

    // mask final state if we do not use a sponge, so it can properly continue
    let final_state = <[Num<E>; 3]>::conditionally_select(
        cs,
        &should_access,
        &final_state,
        &current_memory_sponge_state,
    )?;

    let as_register = read_query.into_register_value(cs)?;

    Ok((
        as_register,
        (initial_state, final_state, new_length, should_access),
    ))
}

/// NOTE: final state is one if we INDEED READ, so extra care should be taken to select and preserve markers
/// if we ever need it or not
pub fn may_be_write_memory<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    should_access: Boolean,
    output: Register<E>,
    timestamp: UInt32<E>,
    location: MemoryLocation<E>,
    current_memory_sponge_state: [Num<E>; 3],
    current_memory_sponge_length: UInt32<E>,
    round_function: &R,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<([Num<E>; 3], [Num<E>; 3], UInt32<E>, Boolean), SynthesisError> {
    use crate::vm::vm_cycle::memory_view::read_view::MemoryKey;
    use crate::vm::vm_cycle::memory_view::write_query::MemoryWriteQuery;

    let MemoryLocation { page, index } = location;
    let memory_key = MemoryKey {
        timestamp,
        memory_page: page,
        memory_index: index,
    };
    let write_query = MemoryWriteQuery::from_key_and_value_witness(cs, memory_key, output)?;

    witness_oracle.push_memory_witness(&write_query, &should_access);

    let raw_query = write_query.into_raw_query(cs)?;

    use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQueriesQueue;
    let (intermediate_states, new_length) =
        MemoryQueriesQueue::push_and_output_states_relation_raw(
            cs,
            &raw_query,
            &should_access,
            current_memory_sponge_state,
            current_memory_sponge_length,
            round_function,
        )?;

    assert_eq!(intermediate_states.len(), 1);

    let (initial_state, final_state) = intermediate_states[0];

    let final_state = <[Num<E>; 3]>::conditionally_select(
        cs,
        &should_access,
        &final_state,
        &current_memory_sponge_state,
    )?;

    Ok((initial_state, final_state, new_length, should_access))
}
