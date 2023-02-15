use std::fmt::Debug;

use super::*;
// use super::execution_context::*;
use crate::scheduler::queues::decommit_query::*;
use crate::scheduler::queues::storage_log::*;
use crate::traits::*;
use cs_derive::*;
use itertools::Itertools;
use rescue_poseidon::{generic_round_function, HashParams};
use std::marker::PhantomData;

#[derive(Derivative, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable)]
#[derivative(Clone, Copy, Debug)]
pub struct ArithmeticFlagsPort<E: Engine> {
    pub overflow_or_less_than: Boolean,
    pub equal: Boolean,
    pub greater_than: Boolean,
    pub _marker: std::marker::PhantomData<E>,
}

impl<E: Engine> CircuitEmpty<E> for ArithmeticFlagsPort<E> {
    fn empty() -> Self {
        Self {
            overflow_or_less_than: Boolean::constant(false),
            equal: Boolean::constant(false),
            greater_than: Boolean::constant(false),
            _marker: std::marker::PhantomData,
        }
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, Default, PartialEq(bound = ""), Eq(bound = ""))]
pub struct ArithmeticFlagsPortWitness {
    pub overflow_or_less_than: bool,
    pub equal: bool,
    pub greater_than: bool,
}

impl<E: Engine> CSWitnessable<E> for ArithmeticFlagsPort<E> {
    type Witness = ArithmeticFlagsPortWitness;

    fn create_witness(&self) -> Option<Self::Witness> {
        let overflow_or_less_than = self.overflow_or_less_than.get_value()?;
        let equal = self.equal.get_value()?;
        let greater_than = self.greater_than.get_value()?;

        let wit = ArithmeticFlagsPortWitness {
            overflow_or_less_than,
            equal,
            greater_than,
        };

        Some(wit)
    }
    fn placeholder_witness() -> Self::Witness {
        ArithmeticFlagsPortWitness::default()
    }
}

use crate::project_ref;

impl<E: Engine> CSAllocatable<E> for ArithmeticFlagsPort<E> {
    fn alloc_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        let overflow_or_less_than =
            Boolean::alloc(cs, project_ref!(witness, overflow_or_less_than).copied())?;
        let equal = Boolean::alloc(cs, project_ref!(witness, equal).copied())?;
        let greater_than = Boolean::alloc(cs, project_ref!(witness, greater_than).copied())?;

        let new = Self {
            overflow_or_less_than,
            equal,
            greater_than,
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }
}

impl<E: Engine> ArithmeticFlagsPort<E> {}

impl<E: Engine> CSPackable<E, 1> for ArithmeticFlagsPort<E> {
    fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        let mut shift = E::Fr::one();
        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&self.overflow_or_less_than, shift);
        shift.double();
        lc.add_assign_boolean_with_coeff(&self.equal, shift);
        shift.double();
        lc.add_assign_boolean_with_coeff(&self.greater_than, shift);

        let encoding = lc.into_num(cs)?;

        Ok([encoding])
    }
}

impl<E: Engine> CircuitFixedLengthEncodable<E, 1> for ArithmeticFlagsPort<E> {
    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; 1], SynthesisError> {
        let packed = self.pack(cs)?;
        Ok(packed)
    }
}

impl<E: Engine> CircuitFixedLengthEncodableExt<E, 1> for ArithmeticFlagsPort<E> {}

impl<E: Engine> CircuitFixedLengthDecodableExt<E, 1> for ArithmeticFlagsPort<E> {
    fn allocate_from_witness<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<Self::Witness>,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_from_witness(cs, witness)
    }
}

impl<E: Engine> CircuitVariableLengthEncodable<E> for ArithmeticFlagsPort<E> {
    fn encoding_length() -> usize {
        1
    }

    fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut result = vec![];
        result.extend(self.pack(cs)?);

        Ok(result)
    }
}

impl<E: Engine> ArithmeticFlagsPort<E> {
    pub fn uninitialized() -> Self {
        ArithmeticFlagsPort {
            overflow_or_less_than: Boolean::constant(false),
            equal: Boolean::constant(false),
            greater_than: Boolean::constant(false),
            _marker: std::marker::PhantomData::<E>,
        }
    }

    pub fn reseted_flags() -> Self {
        ArithmeticFlagsPort {
            overflow_or_less_than: Boolean::constant(false),
            equal: Boolean::constant(false),
            greater_than: Boolean::constant(false),
            _marker: std::marker::PhantomData::<E>,
        }
    }
}

// #[derive(Derivative, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable)]
// #[derivative(Clone, Copy, Debug)]
// pub struct ContextPort<E: Engine, const SWIDTH: usize> {
//     pub current_context: ExecutionContext<E>,
//     pub context_stack_depth: UInt16<E>,
//     pub stack_sponge_state: GenericSpongeState<E, SWIDTH>,
// }

// impl<E: Engine, const SWIDTH: usize> ContextPort<E, SWIDTH> {
//     pub fn empty() -> Self {
//         Self {
//             current_context: ExecutionContext::uninitialized(),
//             context_stack_depth: UInt16::zero(),
//             stack_sponge_state: GenericSpongeState::<E, SWIDTH>::new(),
//         }
//     }
// }

// // we want to initialize empty AlgebraicHashPort in valid state
// // for this purpose we should enforce that: sponge_state_final = sponge(sponge_state_init)
// use std::sync::Once;
// use std::any::{Any, TypeId};

// static mut SPONGE_STATE_FINAL_DEFAULT_VAL: Option<Box<dyn Any>> = None;
// static SPONGE_STATE_FINAL_INIT: Once = Once::new();

// #[derive(Derivative, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable)]
// #[derivative(Clone, Debug)]
// pub struct AlgebraicHashPort<E: Engine, const SWIDTH: usize> {
//     pub sponge_state_init: GenericSpongeState<E, SWIDTH>,
//     pub sponge_state_final: GenericSpongeState<E, SWIDTH>,
// }

// impl<E: Engine, const SWIDTH: usize> Copy for AlgebraicHashPort<E, SWIDTH> {}

// impl<E: Engine, const SWIDTH: usize> AlgebraicHashPort<E, SWIDTH> {
//     pub fn empty() -> Self{
//         assert_eq!(SPONGE_STATE_FINAL_INIT.is_completed(), true);
//         let value_any = unsafe { SPONGE_STATE_FINAL_DEFAULT_VAL.as_ref().unwrap() as &Box<dyn Any> };
//         let raw_state = value_any.downcast_ref::<[Num<E>; SWIDTH]>().unwrap();
//         let sponge_state_final = GenericSpongeState::from_raw(*raw_state);

//         Self {
//             sponge_state_init: GenericSpongeState::empty(),
//             sponge_state_final,
//         }
//     }

//     pub fn init<P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize>(hash_params: &P) {
//         unsafe {
//             SPONGE_STATE_FINAL_INIT.call_once(|| {
//                 let mut raw_hash_state = [E::Fr::zero(); SWIDTH];
//                 generic_round_function(hash_params, &mut raw_hash_state, None);

//                 let mut hash_state = [Num::<E>::zero(); SWIDTH];
//                 for (in_elem, out_elem) in std::array::IntoIter::new(raw_hash_state).zip(hash_state.iter_mut()) {
//                     *out_elem = Num::Constant(in_elem);
//                 }
//                 let boxed: Box<dyn Any> = Box::new(hash_state);
//                 SPONGE_STATE_FINAL_DEFAULT_VAL = Some(boxed);
//             });
//         }
//     }
// }

// #[derive(Derivative, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable)]
// #[derivative(Clone, Debug)]
// pub struct PendingLogPort<E: Engine, const AWIDTH: usize> {
//     pub running_hash : Num<E>,
//     pub first_block: GenericSpongeAbsorbElems<E, AWIDTH>,
//     pub second_block: GenericSpongeAbsorbElems<E, AWIDTH>,
//     pub third_block: GenericSpongeAbsorbElems<E, AWIDTH>,
//     pub pending_log_query_flag: Boolean,
//     pub pending_decommit_query_flag: Boolean,
//     pub pending_double_decommit_query_flag: Boolean,

//     pub any_pending: Option<Boolean>,
//     pub any_decommit_pending: Option<Boolean>
// }

// impl<E: Engine, const AWIDTH: usize> PendingLogPort<E, AWIDTH> {
//     pub fn empty() -> Self{
//         Self {
//             running_hash : Num::<E>::zero(),
//             first_block: GenericSpongeAbsorbElems::<E, AWIDTH>::empty(),
//             second_block: GenericSpongeAbsorbElems::<E, AWIDTH>::empty(),
//             third_block: GenericSpongeAbsorbElems::<E, AWIDTH>::empty(),
//             pending_log_query_flag: Boolean::constant(false),
//             pending_decommit_query_flag: Boolean::constant(false),
//             pending_double_decommit_query_flag: Boolean::constant(false),
//             any_pending: None,
//             any_decommit_pending: None
//         }
//     }

//     pub fn new_log_pending<CS: ConstraintSystem<E>, P: HashParams<E, AWIDTH, SWIDTH>, const SWIDTH: usize>(
//         cs: &mut CS, log: StorageLogRecord<E>, running_hash: Num<E>, should_apply: &Boolean, hash_params: &P
//     ) -> Result<(Self, Num<E>), SynthesisError> {
//         let packed_log = log.pack(cs)?;
//         Self::new_log_pending_impl(cs, &packed_log, running_hash, should_apply, hash_params)
//     }

//     pub fn new_revert_log_pending_impl<CS: ConstraintSystem<E>, P: HashParams<E, AWIDTH, SWIDTH>, const SWIDTH: usize>(
//         cs: &mut CS, packed_log: &[Num<E>], prev_running_hash: Num<E>, running_hash: Num<E>,
//         should_apply: &Boolean, hash_params: &P
//     ) -> Result<Self, SynthesisError> {
//         let third_pending_block = GenericSpongeAbsorbElems::from_slice(
//             &[packed_log[4].clone(), prev_running_hash.clone()]
//         );
//         let pending_port = PendingLogPort {
//             running_hash : running_hash.clone(),
//             first_block: GenericSpongeAbsorbElems::from_slice(&packed_log[0..2]),
//             second_block: GenericSpongeAbsorbElems::from_slice(&packed_log[2..4]),
//             third_block: third_pending_block,
//             pending_log_query_flag: should_apply.clone(),
//             pending_decommit_query_flag: Boolean::constant(false),
//             pending_double_decommit_query_flag: Boolean::constant(false),
//             any_pending: None,
//             any_decommit_pending: None
//         };
//         Ok(pending_port)
//     }

//     pub fn new_log_pending_impl<CS: ConstraintSystem<E>, P: HashParams<E, AWIDTH, SWIDTH>, const SWIDTH: usize>(
//         cs: &mut CS, packed_log: &[Num<E>], running_hash: Num<E>, should_apply: &Boolean, hash_params: &P
//     ) -> Result<(Self, Num<E>), SynthesisError> {
//         let all_has_value = packed_log.iter().chain(iter::once(&running_hash)).all(|x| x.get_value().is_some());
//         let new_running_hash_val = if all_has_value {
//             let mut raw_hash_state = [E::Fr::zero(); SWIDTH];
//             for (a, b) in packed_log.iter().chain(iter::once(&running_hash)).tuples() {
//                 raw_hash_state[0].add_assign(&a.get_value().unwrap());
//                 raw_hash_state[1].add_assign(&b.get_value().unwrap());
//                 generic_round_function(hash_params, &mut raw_hash_state, None);
//             }
//             Some(raw_hash_state[0])
//         }
//         else {
//             None
//         };

//         let new_running_hash = Num::Variable(AllocatedNum::alloc(cs, || new_running_hash_val.grab())?);
//         let third_pending_block = GenericSpongeAbsorbElems::from_slice(
//             &[packed_log[4].clone(), running_hash.clone()]
//         );
//         let pending_port = PendingLogPort {
//             running_hash : new_running_hash.clone(),
//             first_block: GenericSpongeAbsorbElems::from_slice(&packed_log[0..2]),
//             second_block: GenericSpongeAbsorbElems::from_slice(&packed_log[2..4]),
//             third_block: third_pending_block,
//             pending_log_query_flag: should_apply.clone(),
//             pending_decommit_query_flag: Boolean::constant(false),
//             pending_double_decommit_query_flag: Boolean::constant(false),
//             any_pending: None,
//             any_decommit_pending: None
//         };

//         let final_hash = Num::conditionally_select(cs, &should_apply, &new_running_hash, &running_hash)?;
//         Ok((pending_port, final_hash))
//     }

//     pub fn new_decommit_pending<CS: ConstraintSystem<E>>(
//         cs: &mut CS, decommit_query0: DecommitQuery<E>, decommit_query1: DecommitQuery<E>,
//         double_decommit: &Boolean, should_apply: &Boolean
//     ) -> Result<Self, SynthesisError> {
//         let packed_decommit_query0 = decommit_query0.pack(cs)?;
//         let packed_decommit_query1 = decommit_query1.pack(cs)?;
//         let pending_decommit_query_flag = Boolean::and(cs, &double_decommit.not(), &should_apply)?;
//         let pending_double_decommit_query_flag = Boolean::and(cs, &double_decommit, &should_apply)?;

//         let pending_port = PendingLogPort {
//             running_hash : Num::<E>::zero(),
//             first_block: GenericSpongeAbsorbElems::<E, AWIDTH>::from_slice(&packed_decommit_query0[..]),
//             second_block: GenericSpongeAbsorbElems::<E, AWIDTH>::from_slice(&packed_decommit_query1[..]),
//             third_block: GenericSpongeAbsorbElems::<E, AWIDTH>::empty(),
//             pending_log_query_flag: Boolean::constant(false),
//             pending_decommit_query_flag,
//             pending_double_decommit_query_flag,
//             any_pending: None,
//             any_decommit_pending: None
//         };

//         Ok(pending_port)
//     }

//     pub fn is_any_decommit_pending<CS>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError>
//     where CS: ConstraintSystem<E>
//     {
//         if let Some(flag) = self.any_decommit_pending {
//             Ok(flag)
//         }
//         else {
//             let any_decommit_pending = Boolean::or(
//                 cs, &self.pending_decommit_query_flag, &self.pending_double_decommit_query_flag
//             )?;
//             self.any_decommit_pending = Some(any_decommit_pending);
//             Ok(any_decommit_pending)
//         }
//     }

//     pub fn is_any_pending<CS>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError>
//     where CS: ConstraintSystem<E>
//     {
//         if let Some(flag) = self.any_pending {
//             Ok(flag)
//         }
//         else {
//             let any_decommit_pending = self.is_any_decommit_pending(cs)?;
//             let any_pending = Boolean::or(cs, &self.pending_log_query_flag, &any_decommit_pending)?;
//             self.any_pending = Some(any_pending);
//             Ok(any_pending)
//         }
//     }
// }

// impl<E: Engine, const AWIDTH: usize> Copy for PendingLogPort<E, AWIDTH> {}

// #[derive(Derivative, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable)]
// #[derivative(Clone, Debug)]
// pub struct LogQueuePort<E: Engine> {
//     pub direct_queue_len: UInt32<E>,
//     pub direct_queue_hash: Num<E>,
//     pub reverted_queue_len: UInt32<E>,
//     pub reverted_queue_hash: Num<E>
// }

// impl<E: Engine> Copy for LogQueuePort<E> {}

// impl<E: Engine> LogQueuePort<E> {
//     pub fn empty() -> Self{
//         Self {
//             direct_queue_len: UInt32::<E>::zero(),
//             direct_queue_hash: Num::<E>::zero(),
//             reverted_queue_len: UInt32::<E>::zero(),
//             reverted_queue_hash: Num::<E>::zero()
//         }
//     }
// }
