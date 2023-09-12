use super::super::vm_cycle::memory::*;
use super::*;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQueriesQueue;
use crate::vm::primitives::register_view::*;
use crate::vm::vm_cycle::memory_view::read_view::*;
use crate::vm::vm_cycle::memory_view::write_query::*;
use crate::vm::vm_state::PendingRecord;
use franklin_crypto::plonk::circuit::hashes_with_tables::blake2s::gadgets::Reg;
use itertools::Itertools;
use num_traits::ToPrimitive;
use std::sync::Arc;
use zkevm_opcode_defs::definitions::uma::*;

const CELL_BYTE_LEN: u64 = 32;

use cs_derive::*;

use crate::traits::*;

#[derive(CSWitnessable)]
pub struct QuasiFatPtrInUMA<E: Engine> {
    pub absolute_address: UInt32<E>,
    pub page_candidate: UInt32<E>,
    pub incremented_offset: UInt32<E>,
    pub incremented_offset_overflow: Boolean,
    pub skip_memory_access: Boolean,
    pub ignore_reg_updates: Boolean,
    pub should_set_panic: Boolean,
    pub bits_to_cleanup_out_of_bounds: UInt8<E>,
}

impl<E: Engine> QuasiFatPtrInUMA<E> {
    pub(crate) fn parse_and_validate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        input: &RegisterInputView<E>,
        already_panicked: Boolean,
        is_fat_ptr: Boolean,
        _should_increment: Boolean,
        optimizer: &mut OptimizationContext<E>,
    ) -> Result<Self, SynthesisError> {
        // we can never address a range [2^32 - 32..2^32] this way, but we don't care because
        // it's impossible to pay for such memory growth

        let offset = input.u32x8_view.unwrap()[0];
        let page = input.u32x8_view.unwrap()[1];
        let start = input.u32x8_view.unwrap()[2];
        let length = input.u32x8_view.unwrap()[3];

        let (_, in_bounds) = offset.sub_using_delayed_bool_allocation(cs, &length, optimizer)?;

        let mut skip_op = smart_and(cs, &[in_bounds.not(), is_fat_ptr])?;
        skip_op = smart_or(cs, &[skip_op, already_panicked])?;

        // check that we agree in logic with out-of-circuit comparisons
        assert_eq!(
            zkevm_opcode_defs::uma::MAX_OFFSET_TO_DEREF_LOW_U32 + 32u32,
            u32::MAX
        );

        let formal_start = start.mask(cs, &is_fat_ptr)?; // 0 of it's heap/aux heap, otherwise use what we have
        let (absolute_address, _of) =
            formal_start.add_using_delayed_bool_allocation(cs, &offset, optimizer)?;

        let (incremented_offset, incremented_offset_of) =
            offset.add_using_delayed_bool_allocation(cs, &UInt32::from_uint(32), optimizer)?;

        let ignore_reg_updates_due_to_invalid_increment = incremented_offset_of;
        let should_set_panic = smart_or(
            cs,
            &[
                ignore_reg_updates_due_to_invalid_increment,
                already_panicked,
            ],
        )?;

        let is_addressable = incremented_offset_of.not();

        skip_op = smart_or(cs, &[skip_op, is_addressable.not()])?;

        let (mut bytes_out_of_bound, uf) =
            incremented_offset.sub_using_delayed_bool_allocation(cs, &length, optimizer)?;

        bytes_out_of_bound = bytes_out_of_bound.mask(cs, &skip_op.not())?;
        bytes_out_of_bound = bytes_out_of_bound.mask(cs, &uf.not())?;

        let (_, bytes_out_of_bound) = bytes_out_of_bound.div_rem(cs, &UInt32::from_uint(32))?;
        let bits_to_cleanup_out_of_bounds = UInt8::from_num_unchecked(
            bytes_out_of_bound
                .inner
                .mul(cs, &Num::Constant(u64_to_fe(8)))?,
        );

        let new = Self {
            absolute_address,
            page_candidate: page,
            incremented_offset,
            incremented_offset_overflow: incremented_offset_of,
            skip_memory_access: skip_op,
            ignore_reg_updates: ignore_reg_updates_due_to_invalid_increment,
            should_set_panic,
            bits_to_cleanup_out_of_bounds,
        };

        Ok(new)
    }
}

pub(crate) fn apply<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    opcode_carry_parts: &OpcodeCarryParts<E>,
    _global_context: &GlobalContext<E>,
    optimizer: &mut OptimizationContext<E>,
    round_function: &R,
    witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<OpcodePartialApplicationResult<E, PropsMarker>, SynthesisError> {
    let n = cs.get_current_aux_gate_number();

    let uma_heap_read_opcode = zkevm_opcode_defs::Opcode::UMA(UMAOpcode::HeapRead);
    let uma_heap_write_opcode = zkevm_opcode_defs::Opcode::UMA(UMAOpcode::HeapWrite);
    let uma_aux_heap_read_opcode = zkevm_opcode_defs::Opcode::UMA(UMAOpcode::AuxHeapRead);
    let uma_aux_heap_write_opcode = zkevm_opcode_defs::Opcode::UMA(UMAOpcode::AuxHeapWrite);
    let uma_fat_ptr_read_opcode = zkevm_opcode_defs::Opcode::UMA(UMAOpcode::FatPointerRead);

    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(uma_heap_read_opcode);
    let marker_for_allocations_and_alligned_access = CtxMarker::from(uma_heap_read_opcode);
    let marker_for_unaligned_access = CtxMarker::from(uma_heap_read_opcode);

    let is_uma_heap_read = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(uma_heap_read_opcode);
    let is_uma_heap_write = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(uma_heap_write_opcode);
    let is_uma_aux_heap_read = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(uma_aux_heap_read_opcode);
    let is_uma_aux_heap_write = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(uma_aux_heap_write_opcode);
    let is_uma_fat_ptr_read = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(uma_fat_ptr_read_opcode);

    let increment_offset = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[UMA_INCREMENT_FLAG_IDX];

    let access_heap = smart_or(cs, &[is_uma_heap_read, is_uma_heap_write])?;
    let access_aux_heap = smart_or(cs, &[is_uma_aux_heap_read, is_uma_aux_heap_write])?;

    let ctx_ref = &current_state.callstack.current_context;

    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!("Executing UMA");
        if is_uma_heap_read.get_value().unwrap_or(false) {
            println!("Heap read");
        }
        if is_uma_heap_write.get_value().unwrap_or(false) {
            println!("Heap write");
        }
        if is_uma_aux_heap_read.get_value().unwrap_or(false) {
            println!("Aux heap read");
        }
        if is_uma_aux_heap_write.get_value().unwrap_or(false) {
            println!("Aux heap write");
        }
        if is_uma_fat_ptr_read.get_value().unwrap_or(false) {
            println!("Fat ptr read");
        }
    }

    let shifts = compute_shifts::<E::Fr>();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    let mut minus_eight = shifts[3].clone();
    minus_eight.negate();

    // perform basic validation
    let not_a_ptr_when_expected = smart_and(
        cs,
        &[
            should_apply,
            is_uma_fat_ptr_read,
            common_opcode_state.src0_view.is_ptr.not(),
        ],
    )?;

    let quasi_fat_ptr = QuasiFatPtrInUMA::parse_and_validate(
        cs,
        &common_opcode_state.src0_view,
        not_a_ptr_when_expected,
        is_uma_fat_ptr_read,
        increment_offset,
        optimizer,
    )?;

    let set_panic = quasi_fat_ptr.should_set_panic;

    // this one could wrap around, so we account for it. In case if we wrapped we will skip operation anyway
    let max_accessed = quasi_fat_ptr.incremented_offset;

    let heap_max_accessed = max_accessed.mask(cs, &access_heap)?;
    let heap_bound = ctx_ref.saved_context.common_part.heap_upper_bound;
    let (mut heap_growth, uf) =
        heap_max_accessed.sub_using_delayed_bool_allocation(cs, &heap_bound, optimizer)?;
    heap_growth = heap_growth.mask(cs, &uf.not())?; // of we access in bounds then it's 0
    let new_heap_upper_bound =
        UInt32::conditionally_select(cs, &uf, &heap_bound, &heap_max_accessed)?;
    let grow_heap = smart_and(cs, &[access_heap, should_apply])?;

    let aux_heap_max_accessed = max_accessed.mask(cs, &access_aux_heap)?;
    let aux_heap_bound = ctx_ref.saved_context.common_part.aux_heap_upper_bound;
    let (mut aux_heap_growth, uf) =
        aux_heap_max_accessed.sub_using_delayed_bool_allocation(cs, &aux_heap_bound, optimizer)?;
    aux_heap_growth = aux_heap_growth.mask(cs, &uf.not())?; // of we access in bounds then it's 0
    let new_aux_heap_upper_bound =
        UInt32::conditionally_select(cs, &uf, &aux_heap_bound, &aux_heap_max_accessed)?;
    let grow_aux_heap = smart_and(cs, &[access_aux_heap, should_apply])?;

    let mut growth_cost =
        UInt32::conditionally_select(cs, &access_heap, &heap_growth, &UInt32::zero())?;

    growth_cost =
        UInt32::conditionally_select(cs, &access_aux_heap, &aux_heap_growth, &growth_cost)?;

    // and we also penalize for out of bounds accesses
    let highest_128_are_zero = common_opcode_state.src0_view.u128x2_view.unwrap()[1].is_zero(cs)?;
    let bits_64_to_128_are_zero =
        common_opcode_state.src0_view.u64x4_view.unwrap()[1].is_zero(cs)?;
    let bits_32_to_64_are_zero =
        common_opcode_state.src0_view.u32x8_view.unwrap()[1].is_zero(cs)?;

    let top_bits_are_clear = smart_and(
        cs,
        &[
            highest_128_are_zero,
            bits_64_to_128_are_zero,
            bits_32_to_64_are_zero,
        ],
    )?;
    let t = smart_or(
        cs,
        &[
            top_bits_are_clear.not(),
            quasi_fat_ptr.incremented_offset_overflow,
        ],
    )?;
    let heap_access_like = smart_or(cs, &[access_heap, access_aux_heap])?;
    let exception_heap_deref_out_of_bounds = smart_and(cs, &[heap_access_like, t])?;

    growth_cost = UInt32::conditionally_select(
        cs,
        &exception_heap_deref_out_of_bounds,
        &UInt32::from_uint(u32::MAX),
        &growth_cost,
    )?;

    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        println!(
            "Memory growth used {} ergs",
            growth_cost.get_value().unwrap()
        );
    }

    let (ergs_left_after_growth, uf) = opcode_carry_parts
        .preliminary_ergs_left
        .sub_using_delayed_bool_allocation(cs, &growth_cost, optimizer)?;

    let set_panic = smart_or(cs, &[set_panic, uf, exception_heap_deref_out_of_bounds])?; // not enough ergs for growth
                                                                                         // burn all the ergs if not enough
    let ergs_left_after_growth = ergs_left_after_growth.mask(cs, &uf.not())?;

    let should_skip_memory_ops = smart_or(cs, &[quasi_fat_ptr.skip_memory_access, set_panic])?;

    let is_read_access = smart_or(
        cs,
        &[is_uma_heap_read, is_uma_aux_heap_read, is_uma_fat_ptr_read],
    )?;
    let is_write_access = smart_or(cs, &[is_uma_heap_write, is_uma_aux_heap_write])?;

    // NB: Etherium virtual machine is big endian;
    // we need to determine the memory cells' indexes which will be accessed
    // every memory cell is 32 bytes long, the first cell to be accesed has idx = offset / 32
    // if rem = offset % 32 is zero than it is the only one cell to be accessed
    // 1) cell_idx = offset / cell_length, rem = offset % cell_length =>
    // offset = cell_idx * cell_length + rem
    // we should also enforce that cell_idx /in [0, 2^16-1] - this would require range check
    // we should also enforce that 0 <= rem < cell_length = 2^5;
    // rem is actually the byte offset in the first touched cell, to compute bitoffset and shifts
    // we do bit_offset = rem * 8 and then apply shift computing tables
    // flag does_cross_border = rem != 0
    let offset = quasi_fat_ptr.absolute_address.inner;

    let rem = Num::Variable(AllocatedNum::alloc(cs, || {
        let offset_val = offset.get_value().grab()?.into_repr().as_ref()[0];
        let res = u64_to_fe::<E::Fr>(offset_val % CELL_BYTE_LEN);
        Ok(res)
    })?);
    let cell_idx = Num::Variable(AllocatedNum::alloc(cs, || {
        let offset_val = offset.get_value().grab()?.into_repr().as_ref()[0];
        let res = u64_to_fe::<E::Fr>(offset_val / CELL_BYTE_LEN);
        Ok(res)
    })?);

    // enforce that offset = cell_idx * cell_length + rem
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&cell_idx, u64_to_fe::<E::Fr>(CELL_BYTE_LEN));
    lc.add_assign_number_with_coeff(&rem, E::Fr::one());
    lc.add_assign_number_with_coeff(&offset, minus_one.clone());
    lc.enforce_zero(cs)?;

    optimizer.add_range_check(
        cs,
        &cell_idx,
        should_apply,
        marker_for_allocations_and_alligned_access,
        32,
    )?;
    optimizer.add_range_check(
        cs,
        &rem,
        should_apply,
        marker_for_allocations_and_alligned_access,
        5,
    )?;
    let does_cross_border = rem.is_zero(cs)?.not();

    // now we need two shifts constants
    // one defines how many bits from the first word we skip
    // rem < 32, so it doesn't overflow
    let bits_to_skip_from_word_0 =
        UInt8::from_num_unchecked(rem.mul(cs, &Num::Constant(u64_to_fe(8)))?);

    // and second - how many bits we TAKE from the second word
    let mut lc = LinearCombination::zero();
    lc.add_assign_constant(u64_to_fe::<E::Fr>(256));
    // bits_to_skip_from_word_0 <= 31 * 8, so it doesn't underflow
    lc.add_assign_number_with_coeff(&bits_to_skip_from_word_0.inner, minus_one);
    let bits_to_take_from_word_1 = lc.into_num(cs)?;
    // if we do not cross the border then bits_to_take_from_word_1 == 256, but we will reset it into 0 and keep it in mind
    let bits_to_take_from_word_1 = Num::mask(cs, &bits_to_take_from_word_1, &does_cross_border)?;
    let bits_to_take_from_word_1 = UInt8::from_num_unchecked(bits_to_take_from_word_1);

    let shift_low_table = cs.get_table(VM_SHIFT_TO_NUM_LOW_TABLE_NAME)?;
    let shift_high_table = cs.get_table(VM_SHIFT_TO_NUM_HIGH_TABLE_NAME)?;
    let (chunk0, chunk1) =
        super::shift::apply_table(cs, &bits_to_skip_from_word_0, shift_low_table, true)?;
    let (chunk2, chunk3) =
        super::shift::apply_table(cs, &bits_to_skip_from_word_0, shift_high_table, false)?;
    let multiplier_bits_skip_from_word_0 = RegisterInputView {
        u8x32_view: None,
        lowest160: None,
        decomposed_lowest160: None,
        u64x4_view: Some([chunk0, chunk1, chunk2, chunk3]),
        u128x2_view: None,
        u32x8_view: None,
        is_ptr: Boolean::Constant(false),
    };

    let shift_low_table = cs.get_table(VM_SHIFT_TO_NUM_LOW_TABLE_NAME)?;
    let shift_high_table = cs.get_table(VM_SHIFT_TO_NUM_HIGH_TABLE_NAME)?;
    let (chunk0, chunk1) =
        super::shift::apply_table(cs, &bits_to_take_from_word_1, shift_low_table, true)?;
    let (chunk2, chunk3) =
        super::shift::apply_table(cs, &bits_to_take_from_word_1, shift_high_table, false)?;
    let multiplier_bits_take_from_word_1 = RegisterInputView {
        u8x32_view: None,
        lowest160: None,
        decomposed_lowest160: None,
        u64x4_view: Some([chunk0, chunk1, chunk2, chunk3]),
        u128x2_view: None,
        u32x8_view: None,
        is_ptr: Boolean::Constant(false),
    };

    // if access is aligned, then `multiplier_bits_skip_from_word_0` = 1, `multiplier_bits_take_from_word_1` = 1,
    // otherwise it's `multiplier_bits_skip_from_word_0` = 1 << (unalighment * 8), so multiplication will clean up the high bits,
    // and `multiplier_bits_take_from_word_1` = 1 << (32 - unalighment) * 8, so the division will leave high bits in quotient

    // read both memory cells: in what follows we will call the first memory slot A
    // and the second memory Slot B
    let mut mem_queue_state = current_state.memory_queue_state.clone();
    let mut mem_queue_length = current_state.memory_queue_length.clone();

    let mut mem_page = quasi_fat_ptr.page_candidate;
    let page_candidates = [
        (access_heap, opcode_carry_parts.heap_page),
        (access_aux_heap, opcode_carry_parts.aux_heap_page),
    ];
    for (flag, candidate) in page_candidates.into_iter() {
        mem_page = UInt32::conditionally_select(cs, &flag, &candidate, &mem_page)?;
    }

    let a_cell_idx = UInt32::from_num_unchecked(cell_idx);
    // wrap around
    let (b_cell_idx, _of) =
        a_cell_idx.add_using_delayed_bool_allocation(cs, &UInt32::from_uint(1u32), optimizer)?;

    let a_memory_loc = MemoryLocation::<E> {
        page: mem_page.clone(),
        index: a_cell_idx.clone(),
    };
    let b_memory_loc = MemoryLocation::<E> {
        page: mem_page.clone(),
        index: b_cell_idx.clone(),
    };
    let mem_read_timestamp = common_opcode_state.timestamp_for_code_or_src_read.clone();
    let mem_timestamp_write = common_opcode_state.timestamp_for_dst_write.clone();

    let is_unaligned_read = smart_and(
        cs,
        &[
            should_apply,
            does_cross_border,
            should_skip_memory_ops.not(),
        ],
    )?;

    // we yet access the `a` always
    let should_read_a_cell = smart_and(cs, &[should_apply, should_skip_memory_ops.not()])?;
    let should_red_b_cell = is_unaligned_read;
    let mut a = RegisterInputView::<E>::uninitialized();
    let mut b = RegisterInputView::<E>::uninitialized();

    let mut sponge_requests_for_read: Vec<PendingRecord<E, 3>> = vec![];

    for (should_access, mem_loc, out, marker) in [
        (
            should_read_a_cell,
            a_memory_loc.clone(),
            &mut a,
            marker_for_allocations_and_alligned_access,
        ),
        (
            should_red_b_cell,
            b_memory_loc.clone(),
            &mut b,
            marker_for_unaligned_access,
        ),
    ]
    .into_iter()
    {
        let witness_value = witness_oracle.get_memory_witness_for_read(
            mem_read_timestamp.clone(),
            &mem_loc,
            &should_access,
        );

        let witness_value = witness_value.map(|el| el.value);
        let words = split_some_into_fixed_number_of_limbs(witness_value, 64, 4);
        let mut as_u64x4 = [UInt64::<E>::zero(); 4];
        let mut as_u128x2 = [UInt128::<E>::zero(); 2];

        for (input, output) in words.into_iter().zip(as_u64x4.iter_mut()) {
            let val = input.map(|x| x.to_u64().unwrap());
            let allocated = UInt64::allocate_in_optimization_context_with_applicability(
                cs,
                val,
                optimizer,
                should_apply,
                marker,
            )?;

            // if we skip memory op we explicitly enforce that we kind of read zero
            *output =
                UInt64::conditionally_select(cs, &should_access, &allocated, &UInt64::zero())?;
        }

        for (input_pair, output) in as_u64x4.chunks(2).zip(as_u128x2.iter_mut()) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&input_pair[0].inner, shifts[0]);
            lc.add_assign_number_with_coeff(&input_pair[1].inner, shifts[64]);
            *output = UInt128::from_num_unchecked(lc.into_num(cs)?);
        }

        let view = RegisterInputView {
            u8x32_view: None,
            lowest160: None,
            decomposed_lowest160: None,
            u64x4_view: Some(as_u64x4),
            u128x2_view: Some(as_u128x2),
            u32x8_view: None,
            is_ptr: Boolean::Constant(false),
        };

        let MemoryLocation { page, index } = mem_loc.clone();
        let memory_key = MemoryKey {
            timestamp: mem_read_timestamp,
            memory_page: page,
            memory_index: index,
        };

        let read_query = MemoryReadQuery::<E>::from_key_and_reg_view(cs, memory_key, &view)?;
        let raw_query = read_query.into_raw_query(cs)?;

        let (sponges, new_mem_queue_length) = {
            MemoryQueriesQueue::push_and_output_states_relation_raw(
                cs,
                &raw_query,
                &should_access,
                mem_queue_state.clone(),
                mem_queue_length.clone(),
                round_function,
            )?
        };
        assert_eq!(sponges.len(), 1);

        // if should_access.get_value().unwrap_or(false) {
        //     dbg!(Num::get_value_multiple(&mem_queue_state));
        // }

        let (_initial_state, final_state) = sponges[0].clone();
        mem_queue_state = <[Num<E>; 3]>::conditionally_select(
            cs,
            &should_access,
            &final_state,
            &mem_queue_state,
        )?;
        mem_queue_length = new_mem_queue_length;

        // if should_access.get_value().unwrap_or(false) {
        //     dbg!(Num::get_value_multiple(&mem_queue_state));
        // }

        for (initial_state, final_state) in sponges.into_iter() {
            let record = PendingRecord {
                initial_state,
                final_state,
                is_used: should_access,
            };
            sponge_requests_for_read.push(record);
        }

        *out = view;
    }

    let a_as_register = Register {
        inner: a.u128x2_view.unwrap().clone(),
        is_ptr: Boolean::Constant(false),
    };
    let b_as_register = Register {
        inner: b.u128x2_view.unwrap().clone(),
        is_ptr: Boolean::Constant(false),
    };
    // we substitute shifts by multiplications and divisions, and then form a result as an addition,
    // that itself is a XOR in our case as parts after the shifts do not overlap

    // from word `a` we need to skip some bits, so we use multiplication

    // for some unalignment X bytes we will go from 0xaaaa..aaaa to
    // 0x000000....aaaa (X bytes of a) | 0xaaaa....00000 (32 - X bytes of A at the top)
    // and we take the "low" part as the "high" part of unaligned read result, no extra shifts required
    let (a_take_for_read, a_keep_for_write_yet_in_low) = optimizer.add_mul_relation(
        cs,
        &a,
        &multiplier_bits_skip_from_word_0,
        is_unaligned_read,
        marker_for_unaligned_access,
    )?;

    // for word `b` we keep to take some bits from the top, so we use division
    // for some unalignment X bytes we will go from 0xbbbb..bbbb to
    // 0x000000....bbbbb (32 - X bytes of b at the bottom) and 0x0000....bbbb (X bytes of b at the bottom)
    let (b_take_for_read, b_keep_for_write) = optimizer.add_div_relation(
        cs,
        &b,
        &multiplier_bits_take_from_word_1,
        is_unaligned_read,
        marker_for_unaligned_access,
    )?;

    // value of `a_take_for_read` is now in high bits
    // value of `b_take_for_read` is in low bits, so we can perform addition instead of concatenation
    // due to the structure of shifts we can just add them without extra checks

    let read_value_low = UInt128::from_num_unchecked(
        a_take_for_read.u128x2_view.unwrap()[0]
            .inner
            .add(cs, &b_take_for_read.u128x2_view.unwrap()[0].inner)?,
    );
    let read_value_high = UInt128::from_num_unchecked(
        a_take_for_read.u128x2_view.unwrap()[1]
            .inner
            .add(cs, &b_take_for_read.u128x2_view.unwrap()[1].inner)?,
    );
    let read_value_before_cleanup = Register {
        inner: [read_value_low, read_value_high],
        is_ptr: Boolean::constant(false),
    };

    // if we never needed value from the word 1 then we ignore it, and this way an edge case of `multiplier_bits_skip_from_word_0` == 1 and `multiplier_bits_take_from_word_1` == 1 is solved
    let read_value_before_cleanup = Register::conditionally_select(
        cs,
        &does_cross_border,
        &read_value_before_cleanup,
        &a_as_register,
    )?;

    let read_value_view_before_cleanup = RegisterInputView {
        u8x32_view: None,
        lowest160: None,
        decomposed_lowest160: None,
        u64x4_view: None,
        u128x2_view: Some(read_value_before_cleanup.inner),
        u32x8_view: None,
        is_ptr: Boolean::Constant(false),
    };

    // now we need to shift it once again to cleanup from out of bounds part. So we just shift right and left on BE machine

    let shift = quasi_fat_ptr.bits_to_cleanup_out_of_bounds;
    // shift is only non-trivial IF we access pointer
    let shift = UInt8::conditionally_select(cs, &is_uma_fat_ptr_read, &shift, &UInt8::zero())?;

    let shift_low_table = cs.get_table(VM_SHIFT_TO_NUM_LOW_TABLE_NAME)?;
    let shift_high_table = cs.get_table(VM_SHIFT_TO_NUM_HIGH_TABLE_NAME)?;
    let (chunk0, chunk1) = super::shift::apply_table(cs, &shift, shift_low_table, true)?;
    let (chunk2, chunk3) = super::shift::apply_table(cs, &shift, shift_high_table, false)?;
    let full_shift = RegisterInputView {
        u8x32_view: None,
        lowest160: None,
        decomposed_lowest160: None,
        u64x4_view: Some([chunk0, chunk1, chunk2, chunk3]),
        u128x2_view: None,
        u32x8_view: None,
        is_ptr: Boolean::Constant(false),
    };

    // shift right
    let (rshift_q, _) = optimizer.add_div_relation(
        cs,
        &read_value_view_before_cleanup,
        &full_shift,
        is_read_access,
        marker_for_allocations_and_alligned_access,
    )?;

    // shift left
    let (lshift_low, _) = optimizer.add_mul_relation(
        cs,
        &rshift_q,
        &full_shift,
        is_read_access,
        marker_for_allocations_and_alligned_access,
    )?;

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&lshift_low.u64x4_view.unwrap()[0].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&lshift_low.u64x4_view.unwrap()[1].inner, shifts[64]);
    let read_value_low = UInt128::from_num_unchecked(lc.into_num(cs)?);

    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&lshift_low.u64x4_view.unwrap()[2].inner, shifts[0]);
    lc.add_assign_number_with_coeff(&lshift_low.u64x4_view.unwrap()[3].inner, shifts[64]);
    let read_value_high = UInt128::from_num_unchecked(lc.into_num(cs)?);

    let read_value = Register {
        inner: [read_value_low, read_value_high],
        is_ptr: Boolean::Constant(false),
    };

    // for "write" we have to keep the "leftovers"
    // and replace the "inner" part with decomposition of the value from src1
    // to break up the src1 we use `multiplier_bits_take_from_word_1` constant

    let second_option_exec_flag = smart_and(
        cs,
        &[should_apply, is_write_access, should_skip_memory_ops.not()],
    )?; // we do not need set panic here, as it's "inside" of `should_skip_memory_ops`
    let is_unaligned_write = smart_and(cs, &[second_option_exec_flag, does_cross_border])?;

    let written_value = &common_opcode_state.src1_view;
    let written_value_as_register = &common_opcode_state.src1;

    // we take 0xcccc....cccc and shift left by (32 - X) bytes
    // this way we get
    // 0x0000....cccc (32 - X bytes in low) || 0xcccc....0000 (X bytes in high)
    // that is exactly decomposition that we want to overwrite parts of a and b
    let (write_result_into_word_1, mut write_result_into_word_0) = optimizer.add_mul_relation(
        cs,
        &written_value,
        &multiplier_bits_take_from_word_1,
        is_unaligned_write,
        marker_for_unaligned_access,
    )?;
    // note that we did use another marker here - if we are aligned then we must mask the value
    // it also covers the case of `multiplier_bits_take_from_word_1` = 1
    for (w0, src) in write_result_into_word_0
        .u128x2_view
        .as_mut()
        .unwrap()
        .iter_mut()
        .zip(written_value_as_register.inner.iter())
    {
        *w0 = UInt128::conditionally_select(cs, &does_cross_border, &w0, &src)?;
    }

    // we did NOT adjust w1 anyhow for case if access is aligned because result will be discarded anyway later on

    // now we need to move 0x000000....aaaa (X bytes of a) that we had (highest bytes of a that are not affected)
    // into indeed high position
    let (a_keep_shifted, _) = optimizer.add_mul_relation(
        cs,
        &a_keep_for_write_yet_in_low,
        &multiplier_bits_take_from_word_1,
        is_unaligned_write,
        marker_for_unaligned_access,
    )?;
    // it also uses another marker, and we just mask the word_0 written value when needed

    let word_0_to_write_low = UInt128::from_num_unchecked(
        a_keep_shifted.u128x2_view.unwrap()[0]
            .inner
            .add(cs, &write_result_into_word_0.u128x2_view.unwrap()[0].inner)?,
    );
    let word_0_to_write_high = UInt128::from_num_unchecked(
        a_keep_shifted.u128x2_view.unwrap()[1]
            .inner
            .add(cs, &write_result_into_word_0.u128x2_view.unwrap()[1].inner)?,
    );
    let word_0_to_write = Register {
        inner: [word_0_to_write_low, word_0_to_write_high],
        is_ptr: Boolean::Constant(false),
    };
    // mask if we ignored
    let word_0_to_write = Register::conditionally_select(
        cs,
        &does_cross_border,
        &word_0_to_write,
        &written_value_as_register,
    )?;

    let word_1_to_write_low = UInt128::from_num_unchecked(
        b_keep_for_write.u128x2_view.unwrap()[0]
            .inner
            .add(cs, &write_result_into_word_1.u128x2_view.unwrap()[0].inner)?,
    );
    let word_1_to_write_high = UInt128::from_num_unchecked(
        b_keep_for_write.u128x2_view.unwrap()[1]
            .inner
            .add(cs, &write_result_into_word_1.u128x2_view.unwrap()[1].inner)?,
    );
    let word_1_to_write = Register {
        inner: [word_1_to_write_low, word_1_to_write_high],
        is_ptr: Boolean::Constant(false),
    };
    // and mask if it's nonsense, even though we will not use it
    let word_1_to_write =
        Register::conditionally_select(cs, &does_cross_border, &word_1_to_write, &b_as_register)?;

    // now we should write both values in corresponding cells
    let should_write_a_cell = second_option_exec_flag;
    let should_write_b_cell = is_unaligned_write; // we do not tough second cell if it's aligned op

    let mut sponge_requests_for_write: Vec<PendingRecord<E, 3>> = vec![];

    for (should_write, mem_loc, value) in [
        (should_write_a_cell, a_memory_loc, word_0_to_write),
        (should_write_b_cell, b_memory_loc, word_1_to_write),
    ]
    .into_iter()
    {
        let MemoryLocation { page, index } = mem_loc;
        let memory_key = MemoryKey {
            timestamp: mem_timestamp_write,
            memory_page: page,
            memory_index: index,
        };
        let write_query = MemoryWriteQuery::from_key_and_value_witness(cs, memory_key, value)?;

        witness_oracle.push_memory_witness(&write_query, &should_write);

        let raw_query = write_query.into_raw_query(cs)?;

        let (intermediate_states, new_length) =
            MemoryQueriesQueue::push_and_output_states_relation_raw(
                cs,
                &raw_query,
                &should_write,
                mem_queue_state,
                mem_queue_length,
                round_function,
            )?;
        assert_eq!(intermediate_states.len(), 1);

        mem_queue_length = new_length;
        let (_initial_state, final_state) = intermediate_states[0];
        mem_queue_state =
            <[Num<E>; 3]>::conditionally_select(cs, &should_write, &final_state, &mem_queue_state)?;

        for (initial_state, final_state) in intermediate_states.into_iter() {
            let record = PendingRecord {
                initial_state,
                final_state,
                is_used: should_write,
            };
            sponge_requests_for_write.push(record);
        }
    }

    let mut all_sponge_requests = vec![];
    all_sponge_requests.extend(sponge_requests_for_read);
    all_sponge_requests.extend(sponge_requests_for_write);

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(uma_heap_read_opcode);
    opcode_partial_application.applies = should_apply;

    // compute incremented src0
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&quasi_fat_ptr.incremented_offset.inner, shifts[0]);
    lc.add_assign_number_with_coeff(
        &common_opcode_state.src0_view.u32x8_view.unwrap()[1].inner,
        shifts[32],
    );
    lc.add_assign_number_with_coeff(
        &common_opcode_state.src0_view.u64x4_view.unwrap()[1].inner,
        shifts[64],
    );
    let incremented_src_value_low = UInt128::from_num_unchecked(lc.into_num(cs)?);

    let incremented_source_register = Register {
        inner: [
            incremented_src_value_low,
            common_opcode_state.src0_view.u128x2_view.unwrap()[1],
        ],
        is_ptr: common_opcode_state.src0_view.is_ptr,
    };

    let is_write_access_and_increment = smart_and(cs, &[is_write_access, increment_offset])?;
    let update_dst0 = smart_or(cs, &[is_read_access, is_write_access_and_increment])?;

    let should_update_dst0 = smart_and(cs, &[should_apply, update_dst0, set_panic.not()])?;
    let dst0_value = Register::conditionally_select(
        cs,
        &is_write_access_and_increment,
        &incremented_source_register,
        &read_value,
    )?;

    let should_update_dst1 = smart_and(
        cs,
        &[
            should_apply,
            is_read_access,
            increment_offset,
            set_panic.not(),
        ],
    )?;

    opcode_partial_application.dst0_value = Some((should_update_dst0, dst0_value));
    opcode_partial_application.dst1_value = Some((should_update_dst1, incremented_source_register));
    opcode_partial_application.pending_sponges = all_sponge_requests;
    opcode_partial_application.pending_arithmetic_operations = None;
    opcode_partial_application.new_memory_queue_length = Some(mem_queue_length);
    opcode_partial_application.new_memory_queue_state = Some(mem_queue_state);

    // our exception is nothing more than burning all the ergs
    opcode_partial_application.ergs_left = Some(ergs_left_after_growth);
    // set pending exception
    opcode_partial_application.pending_exception = Some(set_panic);
    // account for grwoth of max addressed memory
    opcode_partial_application.new_heap_upper_bound = Some((grow_heap, new_heap_upper_bound));
    opcode_partial_application.new_aux_heap_upper_bound =
        Some((grow_aux_heap, new_aux_heap_upper_bound));

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!(
        "{} gates used for opcode {:?}",
        gates_used, uma_heap_read_opcode
    );
    // dbg!(_message);

    Ok(opcode_partial_application)
}
