use super::execution_context::*;
use super::primitives::rescue_sponge::*;
use super::primitives::*;
use super::*;
use crate::glue::traits::*;
use crate::project;
use crate::traits::*;
use cs_derive::*;
use num_traits::Zero;
use std::marker::PhantomData;

// here we store only part of the context that keeps the data that
// needs to be stored or restored between the calls

pub const EXECUTION_CONTEXT_RECORD_ENCODING_LEN: usize = 6;
pub const CONTEXT_EXTENSION_ELEMENT_IDX: usize = 5;
pub const CONTEXT_EXTENSION_OFFSET: usize = 218;

// repeated note on how joining of rollback queues work
// - first we use some non-determinism to declare a rollback_tail == current_rollback_head
// - when we do write we add element into front as forward_tail = hash(forward_tail, log_element)
// and also declare some rollback_head, such that current_rollback_head = hash(rollback_head, log_element)
// - if we return "ok" then we join as
//      - forward_tail = callee forward_tail
//      - rollback_head = callee rollback_head
// - else
//      - forward_tail = rollback_tail
//      - caller's rollback_head is unchanged
//      - require callee forward_tail == rollback_head
//
// so to proceed with joining we need to only maintain
// - global forward_tail and length of the forward segment
// - per-context declared rollback_tail
// - per-context computed rollback segment length
// - per-context rollback_head

// per-context parts are saved below

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct ExecutionContextRecordCommomPart<E: Engine> {
    pub this: UInt160<E>, // unfortunately delegatecall mangles this field - it can not be restored from callee's caller
    pub caller: UInt160<E>,
    pub code_address: UInt160<E>,

    pub code_page: UInt32<E>,
    pub base_page: UInt32<E>,

    pub heap_upper_bound: UInt32<E>,
    pub aux_heap_upper_bound: UInt32<E>,

    pub reverted_queue_head: Num<E>,
    pub reverted_queue_tail: Num<E>,
    pub reverted_queue_segment_len: UInt32<E>,

    pub pc: UInt16<E>,
    pub sp: UInt16<E>,
    pub exception_handler_loc: UInt16<E>,
    pub ergs_remaining: UInt32<E>,
    pub pubdata_bytes_remaining: UInt16<E>,

    pub is_static_execution: Boolean,
    pub is_kernel_mode: Boolean,

    pub this_shard_id: UInt8<E>,
    pub caller_shard_id: UInt8<E>,
    pub code_shard_id: UInt8<E>,

    pub context_u128_value_composite: [UInt64<E>; 2],
}

impl<E: Engine> Copy for ExecutionContextRecordCommomPart<E> {}

impl<E: Engine> ExecutionContextRecordCommomPart<E> {
    pub fn uninitialized() -> Self {
        ExecutionContextRecordCommomPart {
            this: UInt160::<E>::zero(),
            caller: UInt160::<E>::zero(),
            code_address: UInt160::<E>::zero(),
            code_page: UInt32::<E>::zero(),
            base_page: UInt32::<E>::zero(),

            heap_upper_bound: UInt32::<E>::zero(),
            aux_heap_upper_bound: UInt32::<E>::zero(),

            reverted_queue_head: Num::<E>::zero(),
            reverted_queue_tail: Num::<E>::zero(),
            reverted_queue_segment_len: UInt32::<E>::zero(),

            pc: UInt16::<E>::zero(),
            sp: UInt16::<E>::zero(),
            exception_handler_loc: UInt16::<E>::zero(),
            ergs_remaining: UInt32::<E>::zero(),
            pubdata_bytes_remaining: UInt16::<E>::zero(),

            is_static_execution: Boolean::constant(false),
            is_kernel_mode: Boolean::constant(false),

            this_shard_id: UInt8::<E>::zero(),
            caller_shard_id: UInt8::<E>::zero(),
            code_shard_id: UInt8::<E>::zero(),

            context_u128_value_composite: [UInt64::<E>::zero(); 2],
        }
    }

    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; EXECUTION_CONTEXT_RECORD_ENCODING_LEN], SynthesisError> {
        let val_0 = self.reverted_queue_head;
        let val_1 = self.reverted_queue_tail;

        let shifts = compute_shifts::<E::Fr>();

        let mut lc = LinearCombination::<E>::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.this.inner, shifts[shift]);
        shift += 160;
        lc.add_assign_number_with_coeff(&self.context_u128_value_composite[0].inner, shifts[shift]);
        shift += 64;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let val_2 = lc.into_num(cs)?;

        let mut lc = LinearCombination::<E>::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.caller.inner, shifts[shift]);
        shift += 160;
        lc.add_assign_number_with_coeff(&self.context_u128_value_composite[1].inner, shifts[shift]);
        shift += 64;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let val_3 = lc.into_num(cs)?;

        let mut lc = LinearCombination::<E>::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.code_address.inner, shifts[shift]);
        shift += 160;
        lc.add_assign_number_with_coeff(&self.heap_upper_bound.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.aux_heap_upper_bound.inner, shifts[shift]);
        shift += 32;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let val_4 = lc.into_num(cs)?;

        let mut lc = LinearCombination::<E>::zero();
        let mut shift = 0;
        lc.add_assign_number_with_coeff(&self.code_page.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.base_page.inner, shifts[shift]);
        shift += 32;
        // 64
        lc.add_assign_number_with_coeff(&self.reverted_queue_segment_len.inner, shifts[shift]);
        shift += 32;
        lc.add_assign_number_with_coeff(&self.ergs_remaining.inner, shifts[shift]);
        shift += 32;
        // 128
        lc.add_assign_number_with_coeff(&self.sp.inner, shifts[shift]);
        shift += 16;
        lc.add_assign_number_with_coeff(&self.exception_handler_loc.inner, shifts[shift]);
        shift += 16;
        // 160
        lc.add_assign_number_with_coeff(&self.pc.inner, shifts[shift]);
        shift += 16;
        lc.add_assign_number_with_coeff(&self.this_shard_id.inner, shifts[shift]);
        shift += 8;
        lc.add_assign_number_with_coeff(&self.caller_shard_id.inner, shifts[shift]);
        shift += 8;
        // 192
        lc.add_assign_number_with_coeff(&self.pubdata_bytes_remaining.inner, shifts[shift]);
        shift += 16;
        // 208
        lc.add_assign_number_with_coeff(&self.code_shard_id.inner, shifts[shift]);
        shift += 8;
        // 216
        lc.add_assign_boolean_with_coeff(&self.is_static_execution, shifts[shift]);
        shift += 1;
        lc.add_assign_boolean_with_coeff(&self.is_kernel_mode, shifts[shift]);
        shift += 1;
        // 218
        let val_5 = lc.into_num(cs)?;
        assert!(shift <= E::Fr::CAPACITY as usize);
        assert_eq!(CONTEXT_EXTENSION_OFFSET, shift);

        Ok([val_0, val_1, val_2, val_3, val_4, val_5])
    }

    pub fn allocate_in_optimization_context_with_applicability<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        wit: Option<ExecutionContextRecordCommomPartWitness<E>>,
        ctx: &mut OptimizationContext<E>,
        should_apply: &Boolean,
        marker: CtxMarker,
    ) -> Result<Self, SynthesisError> {
        let this = UInt160::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, this),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let caller = UInt160::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, caller),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let code_address = UInt160::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, code_address),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let code_page = UInt32::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, code_page),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let base_page = UInt32::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, base_page),
            ctx,
            should_apply.clone(),
            marker,
        )?;

        let heap_upper_bound = UInt32::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, heap_upper_bound),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let aux_heap_upper_bound = UInt32::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, aux_heap_upper_bound),
            ctx,
            should_apply.clone(),
            marker,
        )?;

        let reverted_queue_head = Num::alloc(cs, project!(wit, reverted_queue_head))?;
        let reverted_queue_tail = Num::alloc(cs, project!(wit, reverted_queue_tail))?;
        let reverted_queue_segment_len =
            UInt32::allocate_in_optimization_context_with_applicability(
                cs,
                project!(wit, reverted_queue_segment_len),
                ctx,
                should_apply.clone(),
                marker,
            )?;

        let pc = UInt16::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, pc),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let sp = UInt16::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, sp),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let ergs_remaining = UInt32::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, ergs_remaining),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let pubdata_bytes_remaining = UInt16::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, pubdata_bytes_remaining),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let exception_handler_loc = UInt16::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, exception_handler_loc),
            ctx,
            should_apply.clone(),
            marker,
        )?;

        let is_static_execution =
            Boolean::Is(AllocatedBit::alloc(cs, project!(wit, is_static_execution))?);
        let is_kernel_mode = Boolean::Is(AllocatedBit::alloc(cs, project!(wit, is_kernel_mode))?);

        let this_shard_id = UInt8::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, this_shard_id),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let caller_shard_id = UInt8::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, caller_shard_id),
            ctx,
            should_apply.clone(),
            marker,
        )?;
        let code_shard_id = UInt8::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, code_shard_id),
            ctx,
            should_apply.clone(),
            marker,
        )?;

        let context_u128_composite_0 = UInt64::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, context_u128_value_composite).map(|el| el[0]),
            ctx,
            should_apply.clone(),
            marker,
        )?;

        let context_u128_composite_1 = UInt64::allocate_in_optimization_context_with_applicability(
            cs,
            project!(wit, context_u128_value_composite).map(|el| el[1]),
            ctx,
            should_apply.clone(),
            marker,
        )?;

        let res = ExecutionContextRecordCommomPart {
            this,
            caller,
            code_address,
            code_page,
            base_page,

            heap_upper_bound,
            aux_heap_upper_bound,

            reverted_queue_head,
            reverted_queue_tail,
            reverted_queue_segment_len,

            pc,
            sp,
            ergs_remaining,
            pubdata_bytes_remaining,
            exception_handler_loc,

            is_static_execution,
            is_kernel_mode,

            this_shard_id,
            caller_shard_id,
            code_shard_id,

            context_u128_value_composite: [context_u128_composite_0, context_u128_composite_1],
        };

        Ok(res)
    }
}

use crate::vm::primitives::small_uints::IntoFr;

pub fn scale_and_accumulate<E: Engine, T: IntoFr<E>>(
    into: &mut E::Fr,
    input: T,
    shifts: &[E::Fr],
    shift: usize,
) {
    let mut t = input.into_fr();
    t.mul_assign(&shifts[shift]);
    into.add_assign(&t);
}

impl<E: Engine> ExecutionContextRecordCommomPartWitness<E> {
    pub fn pack(&self) -> [E::Fr; EXECUTION_CONTEXT_RECORD_ENCODING_LEN] {
        let val_0: E::Fr = self.reverted_queue_head;
        let val_1: E::Fr = self.reverted_queue_tail;

        let shifts = compute_shifts::<E::Fr>();

        let mut lc = E::Fr::zero();
        let mut shift = 0;
        scale_and_accumulate::<E, _>(&mut lc, self.this, &shifts, shift);
        shift += 160;
        scale_and_accumulate::<E, _>(
            &mut lc,
            self.context_u128_value_composite[0],
            &shifts,
            shift,
        );
        shift += 64;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let val_2 = lc;

        let mut lc = E::Fr::zero();
        let mut shift = 0;
        scale_and_accumulate::<E, _>(&mut lc, self.caller, &shifts, shift);
        shift += 160;
        scale_and_accumulate::<E, _>(
            &mut lc,
            self.context_u128_value_composite[1],
            &shifts,
            shift,
        );
        shift += 64;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let val_3 = lc;

        let mut lc = E::Fr::zero();
        let mut shift = 0;
        scale_and_accumulate::<E, _>(&mut lc, self.code_address, &shifts, shift);
        shift += 160;
        scale_and_accumulate::<E, _>(&mut lc, self.heap_upper_bound, &shifts, shift);
        shift += 32;
        scale_and_accumulate::<E, _>(&mut lc, self.aux_heap_upper_bound, &shifts, shift);
        shift += 32;
        assert!(shift <= E::Fr::CAPACITY as usize);
        let val_4 = lc;

        let mut lc = E::Fr::zero();
        let mut shift = 0;
        scale_and_accumulate::<E, _>(&mut lc, self.code_page, &shifts, shift);
        shift += 32;
        scale_and_accumulate::<E, _>(&mut lc, self.base_page, &shifts, shift);
        shift += 32;
        // 64
        scale_and_accumulate::<E, _>(&mut lc, self.reverted_queue_segment_len, &shifts, shift);
        shift += 32;
        scale_and_accumulate::<E, _>(&mut lc, self.ergs_remaining, &shifts, shift);
        shift += 32;
        // 128
        scale_and_accumulate::<E, _>(&mut lc, self.sp, &shifts, shift);
        shift += 16;
        scale_and_accumulate::<E, _>(&mut lc, self.exception_handler_loc, &shifts, shift);
        shift += 16;
        // 160
        scale_and_accumulate::<E, _>(&mut lc, self.pc, &shifts, shift);
        shift += 16;
        scale_and_accumulate::<E, _>(&mut lc, self.this_shard_id, &shifts, shift);
        shift += 8;
        scale_and_accumulate::<E, _>(&mut lc, self.caller_shard_id, &shifts, shift);
        shift += 8;
        // 192
        scale_and_accumulate::<E, _>(&mut lc, self.pubdata_bytes_remaining, &shifts, shift);
        shift += 16;
        // 208
        scale_and_accumulate::<E, _>(&mut lc, self.code_shard_id, &shifts, shift);
        shift += 8;
        // 216
        scale_and_accumulate::<E, _>(&mut lc, self.is_static_execution, &shifts, shift);
        shift += 1;
        scale_and_accumulate::<E, _>(&mut lc, self.is_kernel_mode, &shifts, shift);
        shift += 1;
        // 218
        let val_5 = lc;
        assert!(shift <= E::Fr::CAPACITY as usize);
        assert_eq!(CONTEXT_EXTENSION_OFFSET, shift);

        [val_0, val_1, val_2, val_3, val_4, val_5]
    }
}

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct ExecutionContextRecordExtension<E: Engine> {
    // set only for near call
    pub is_local_call: Boolean,
    pub marker: std::marker::PhantomData<E>,
}

impl<E: Engine> Copy for ExecutionContextRecordExtension<E> {}

impl<E: Engine> ExecutionContextRecordExtension<E> {
    pub fn uninitialized() -> Self {
        ExecutionContextRecordExtension {
            is_local_call: Boolean::constant(false),
            marker: std::marker::PhantomData::<E>,
        }
    }

    pub fn add_to_packing<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        packing: &mut [Num<E>; EXECUTION_CONTEXT_RECORD_ENCODING_LEN],
    ) -> Result<(), SynthesisError> {
        let shifts = compute_shifts::<E::Fr>();
        let shift_fr = shifts[CONTEXT_EXTENSION_OFFSET];

        let mut lc = LinearCombination::zero();
        lc.add_assign_number_with_coeff(&packing[CONTEXT_EXTENSION_ELEMENT_IDX], E::Fr::one());
        lc.add_assign_boolean_with_coeff(&self.is_local_call, shift_fr);
        packing[CONTEXT_EXTENSION_ELEMENT_IDX] = lc.into_num(cs)?;

        Ok(())
    }

    pub fn allocate_in_optimization_context_with_applicability<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        wit: Option<ExecutionContextRecordExtensionWitness<E>>,
        _ctx: &mut OptimizationContext<E>,
        _should_apply: &Boolean,
        _marker: CtxMarker,
    ) -> Result<Self, SynthesisError> {
        let is_local_call = Boolean::Is(AllocatedBit::alloc(cs, project!(wit, is_local_call))?);
        let res = ExecutionContextRecordExtension {
            is_local_call,
            marker: std::marker::PhantomData,
        };

        Ok(res)
    }
}

impl<E: Engine> ExecutionContextRecordExtensionWitness<E> {
    pub fn add_to_packing(&self, packing: &mut [E::Fr; EXECUTION_CONTEXT_RECORD_ENCODING_LEN]) {
        let shifts = compute_shifts::<E::Fr>();

        scale_and_accumulate::<E, _>(
            &mut packing[CONTEXT_EXTENSION_ELEMENT_IDX],
            self.is_local_call,
            &shifts,
            CONTEXT_EXTENSION_OFFSET,
        );
    }
}

#[derive(Derivative, CSWitnessable, CSAllocatable, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct ExecutionContextRecord<E: Engine> {
    pub common_part: ExecutionContextRecordCommomPart<E>,
    pub extension: ExecutionContextRecordExtension<E>,
}

impl<E: Engine> Copy for ExecutionContextRecord<E> {}

impl<E: Engine> ExecutionContextRecord<E> {
    pub fn uninitialized() -> Self {
        ExecutionContextRecord {
            common_part: ExecutionContextRecordCommomPart::<E>::uninitialized(),
            extension: ExecutionContextRecordExtension::<E>::uninitialized(),
        }
    }

    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; EXECUTION_CONTEXT_RECORD_ENCODING_LEN], SynthesisError> {
        let mut packing = self.common_part.pack(cs)?;
        self.extension.add_to_packing(cs, &mut packing)?;
        Ok(packing)
    }

    pub fn allocate_in_optimization_context_with_applicability<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        wit: Option<ExecutionContextRecordWitness<E>>,
        ctx: &mut OptimizationContext<E>,
        should_apply: &Boolean,
        marker: CtxMarker,
    ) -> Result<Self, SynthesisError> {
        let (common_part_wit, extension_wit) = match wit {
            Some(wit) => (Some(wit.common_part), Some(wit.extension)),
            None => (None, None),
        };

        let common_part =
            ExecutionContextRecordCommomPart::allocate_in_optimization_context_with_applicability(
                cs,
                common_part_wit,
                ctx,
                should_apply,
                marker,
            )?;
        let extension =
            ExecutionContextRecordExtension::allocate_in_optimization_context_with_applicability(
                cs,
                extension_wit,
                ctx,
                should_apply,
                marker,
            )?;

        Ok(ExecutionContextRecord {
            common_part,
            extension,
        })
    }
}

impl<E: Engine> ExecutionContextRecordWitness<E> {
    pub fn pack(&self) -> [E::Fr; EXECUTION_CONTEXT_RECORD_ENCODING_LEN] {
        let mut packing = self.common_part.pack();
        self.extension.add_to_packing(&mut packing);

        packing
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, EXECUTION_CONTEXT_RECORD_ENCODING_LEN>
    for ExecutionContextRecord<E>
{
    fn encode<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; EXECUTION_CONTEXT_RECORD_ENCODING_LEN], SynthesisError> {
        let packed = self.pack(cs)?;
        Ok(packed)
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, EXECUTION_CONTEXT_RECORD_ENCODING_LEN>
    for ExecutionContextRecord<E>
{
}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, EXECUTION_CONTEXT_RECORD_ENCODING_LEN>
    for ExecutionContextRecord<E>
{
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> CircuitVariableLengthEncodable<E> for ExecutionContextRecord<E> {
    fn encoding_length() -> usize {
        EXECUTION_CONTEXT_RECORD_ENCODING_LEN
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut result = vec![];
        result.extend(self.pack(cs)?);

        Ok(result)
    }
}

use crate::scheduler::queues::FixedWidthEncodingSpongeLikeQueue;
pub(crate) type CallstackSpongeQueue<E, const AWIDTH: usize, const SWIDTH: usize> =
    FixedWidthEncodingSpongeLikeQueue<
        E,
        ExecutionContextRecord<E>,
        EXECUTION_CONTEXT_RECORD_ENCODING_LEN,
        AWIDTH,
        SWIDTH,
    >;

// #[derive(Derivative)]
// #[derivative(Clone, Debug)]
// struct ContextStackEntry<E: Engine, const SW: usize> {
//     hash_state_wit: [Option<E::Fr>; SW],
//     context_record_wit: Option<ExecutionContextRecordWitness<E>>,
// }

// #[derive(Derivative)]
// #[derivative(Clone, Debug)]
// pub struct ContextStack<E: Engine, const SW: usize>{
//     entries: Vec<ContextStackEntry<E, SW>>
// }

// impl<E: Engine, const SW: usize> ContextStack<E, SW> {
//     pub fn new() -> Self {
//         let mut context_stack = ContextStack {
//             entries: Vec::with_capacity(MAX_CONTEXT_STACK_DEPTH)
//         };
//         let record = ExecutionContextRecord::uninitialized();
//         context_stack.push(&Boolean::constant(true), &GenericSpongeState::empty(), &record);
//         context_stack
//     }

//     pub fn reset(&mut self) {
//         self.entries.clear();
//         let record = ExecutionContextRecord::uninitialized();
//         self.push(&Boolean::constant(true), &GenericSpongeState::empty(), &record);
//     }

//     pub fn push(
//         &mut self,
//         condition: &Boolean,
//         hash_state: &GenericSpongeState<E, SW>,
//         context_record: &ExecutionContextRecord<E>
//     ) {
//         let hash_state_wit = hash_state.get_witness();
//         let context_record_wit = context_record.create_witness();
//         let entry = ContextStackEntry {
//             hash_state_wit,
//             context_record_wit
//         };
//         if condition.get_value().unwrap_or(false) {
//             self.entries.push(entry)
//         }
//     }

//     fn pop_inner(&mut self, flag: &Boolean) -> (Option<ExecutionContextRecordWitness<E>>, [Option<E::Fr>; SW])
//     {
//         let use_context_stack = flag.get_value().unwrap_or(false) && (self.entries.len() != 0);
//         let (record_witness, context_state_witness) = if use_context_stack {
//             let entry = self.entries.pop().unwrap();
//             (entry.context_record_wit, entry.hash_state_wit)
//         }
//         else {
//             (
//                 Some(ExecutionContextRecord::<E>::placeholder_witness()),
//                 GenericSpongeState::<E, SW>::placeholder_witness()
//             )
//         };
//         (record_witness, context_state_witness)
//     }

//     pub fn pop<CS: ConstraintSystem<E>>(
//         &mut self,
//         cs: &mut CS,
//         condition: &Boolean
//     ) -> Result<(ExecutionContextRecord<E>, GenericSpongeState<E, SW>), SynthesisError>
//     {
//         let (record_witness, context_state_witness) = self.pop_inner(condition);
//         let record = ExecutionContextRecord::alloc_from_witness(cs, record_witness)?;
//         let context_state = GenericSpongeState::alloc_from_witness(cs, context_state_witness)?;
//         Ok((record, context_state))
//     }

//     pub fn pop_with_optimization_context<CS: ConstraintSystem<E>>(
//         &mut self,
//         cs: &mut CS,
//         condition: &Boolean,
//         ctx: &mut OptimizationContext<E>,
//         marker: CtxMarker
//     ) -> Result<(ExecutionContextRecord<E>, GenericSpongeState<E, SW>), SynthesisError>
//     {
//         let (record_witness, context_state_witness) = self.pop_inner(condition);
//         let record = ExecutionContextRecord::allocate_in_optimization_context_with_applicability(
//             cs, record_witness, ctx, condition, marker
//         )?;
//         let context_state = GenericSpongeState::alloc_from_witness(cs, context_state_witness)?;
//         Ok((record, context_state))
//     }
// }
