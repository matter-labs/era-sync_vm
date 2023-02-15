use cs_derive::CSSelectable;

use super::primitives::register_view::*;
use super::primitives::utils::multiselection_using_linear_combination;
use super::primitives::{UInt128, UInt64};
use super::VM_RANGE_CHECK_TABLE_WIDTH;
use super::*;
// use super::opcodes::*;
use super::structural_eq::*;
use crate::bellman::plonk::better_better_cs::cs::{ArithmeticTerm, MainGateTerm, Variable};
use crate::utils::IdentifyFirstLast;

use std::any::Any;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::mem;

use crate::vm::vm_cycle::pre_state::PendingArithmeticRelation;
type PendingVec<E> = Vec<(PendingArithmeticRelation<E>, Boolean)>;

// all selections before actual range checking will be done over elements of at least
// threshold bits in length
pub const RANGE_CHECK_THRESHOLD: usize = 64;
pub const CALL_HASH_PORT_MARKER: usize = 20;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CtxMarker {
    idx: u8,
}

use zkevm_opcode_defs::NUM_OPCODES;

impl CtxMarker {
    pub fn advance(self) -> Self {
        use num_traits::FromPrimitive;
        CtxMarker {
            idx: self.idx + (NUM_OPCODES as u8),
        }
    }

    pub fn dummy_marker() -> Self {
        CtxMarker { idx: 0xff }
    }

    pub fn pending_marker() -> Self {
        CtxMarker { idx: 0xee }
    }
}

impl From<zkevm_opcode_defs::Opcode> for CtxMarker {
    fn from(opcode: zkevm_opcode_defs::Opcode) -> Self {
        let idx = match opcode {
            zkevm_opcode_defs::Opcode::Invalid(_) => unimplemented!(),
            zkevm_opcode_defs::Opcode::Nop(_) => 0,
            zkevm_opcode_defs::Opcode::Add(_) => 1,
            zkevm_opcode_defs::Opcode::Sub(_) => 2,
            zkevm_opcode_defs::Opcode::Mul(_) => 3,
            zkevm_opcode_defs::Opcode::Div(_) => 4,
            zkevm_opcode_defs::Opcode::Jump(_) => 5,
            zkevm_opcode_defs::Opcode::Ptr(_) => 6,
            zkevm_opcode_defs::Opcode::Context(_) => 7,
            zkevm_opcode_defs::Opcode::Shift(_) => 8,
            zkevm_opcode_defs::Opcode::Binop(_) => 9,
            zkevm_opcode_defs::Opcode::NearCall(_)
            | zkevm_opcode_defs::Opcode::FarCall(_)
            | zkevm_opcode_defs::Opcode::Ret(_) => 10,
            zkevm_opcode_defs::Opcode::Log(_) => 11,
            zkevm_opcode_defs::Opcode::UMA(_) => 12,
        };

        CtxMarker { idx }
    }
}

impl From<u8> for CtxMarker {
    fn from(byte: u8) -> Self {
        CtxMarker { idx: byte }
    }
}

fn has_unique_elements<T>(iter: T) -> bool
where
    T: IntoIterator,
    T::Item: Eq + Hash,
{
    let mut uniq = HashSet::new();
    iter.into_iter().all(move |x| uniq.insert(x))
}

// Moves all duplicates to the end of the slice,
//where elements are considered to be duplicates if they resolve to the same key.
// Returns two slices. The first contains no duplicates elements in no specific order.
// The second contains all the duplicates in no specified order.
pub fn partition_dedup_by_key<T, K, F>(arr: Vec<T>, key: F) -> (Vec<T>, Vec<T>)
where
    F: Fn(&T) -> K,
    K: Eq + Hash,
{
    let len = arr.len();
    if len <= 1 {
        return (arr, vec![]);
    }

    let mut uniq = HashSet::new();

    let mut partition = vec![];
    let mut other = vec![];

    for el in arr.into_iter() {
        let k = key(&el);
        if !uniq.contains(&k) {
            uniq.insert(k);
            partition.push(el)
        } else {
            other.push(el);
        }
    }

    (partition, other)
}

// represents a boolean value for which we haven't yet enofrced that flag * (1 - flag) == 0
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct UncheckedBoolean<E: Engine> {
    pub raw_flag: Num<E>,
}

impl<E: Engine> UncheckedBoolean<E> {
    pub fn get_value(&self) -> Option<E::Fr> {
        self.raw_flag.get_value()
    }

    pub fn constant(flag: bool) -> Self {
        let fr = if flag { E::Fr::one() } else { E::Fr::zero() };

        UncheckedBoolean {
            raw_flag: Num::Constant(fr),
        }
    }

    pub fn alloc_from_witness<CS>(cs: &mut CS, wit: Option<bool>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let allocated_var = AllocatedNum::alloc(cs, || {
            wit.map(|x| if x { E::Fr::one() } else { E::Fr::zero() })
                .grab()
        })?;
        let raw = Num::Variable(allocated_var);

        Ok(UncheckedBoolean { raw_flag: raw })
    }

    fn into_boolean_impl(&self) -> Boolean {
        //dirty hack, but I really don't want AllocatedBit provate methods to be exposed to outside world
        use std::mem::transmute;

        #[derive(Clone, Debug)]
        pub struct AllocatedBitShadow {
            pub variable: Variable,
            pub value: Option<bool>,
        }

        let allocated_var_shadow = AllocatedBitShadow {
            variable: self.raw_flag.get_variable().get_variable(),
            value: self.raw_flag.get_value().map(|x| !x.is_zero()),
        };
        let allocated_var: AllocatedBit = unsafe { std::mem::transmute(allocated_var_shadow) };

        Boolean::Is(allocated_var)
    }

    pub fn into_boolean_unchecked(&self) -> Boolean {
        assert!(!self.raw_flag.is_constant());
        self.into_boolean_impl()
    }

    pub fn into_boolean_checked<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError> {
        let res = self.into_boolean_impl();
        let var = res.get_variable().unwrap().get_variable();

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        let mut gate_term = MainGateTerm::new();
        let mut multiplicative_term = ArithmeticTerm::from_variable(var);
        multiplicative_term = multiplicative_term.mul_by_variable(var);
        gate_term.add_assign(multiplicative_term);
        gate_term.sub_assign(ArithmeticTerm::from_variable(var));
        cs.allocate_main_gate(gate_term)?;

        Ok(res)
    }
}

#[derive(Derivative, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct AsU64x4<E: Engine> {
    pub inner: [UInt64<E>; 4],
}

impl<E: Engine> From<&RegisterInputView<E>> for AsU64x4<E> {
    fn from(view: &RegisterInputView<E>) -> Self {
        Self {
            inner: view.u64x4_view.unwrap().clone(),
        }
    }
}

impl<E: Engine> AsU64x4<E> {
    pub fn zero() -> Self {
        Self {
            inner: [UInt64::zero(); 4],
        }
    }

    #[track_caller]
    pub fn alloc_unchecked<CS>(cs: &mut CS, value: Option<BigUint>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            new.inner[i] = UInt64 { inner: allocated };
        }

        Ok(new)
    }

    #[track_caller]
    pub fn alloc_checked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        applies: Boolean,
        ctx: &mut OptimizationContext<E>,
        marker: CtxMarker,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            ctx.add_range_check(cs, &allocated, applies, marker, 64)?;
            new.inner[i] = UInt64 { inner: allocated };
        }

        Ok(new)
    }

    #[track_caller]
    pub fn alloc_pended<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        applies: Boolean,
        pended_ops: &mut PendingVec<E>,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut new = Self::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            let pended_range_check = {
                (
                    PendingArithmeticRelation::RangeCheckRelation((allocated.clone(), 64)),
                    applies,
                )
            };
            pended_ops.push(pended_range_check);
            new.inner[i] = UInt64 { inner: allocated };
        }

        Ok(new)
    }

    pub fn get_value(&self) -> Option<BigUint> {
        let mut base = BigUint::from(0u64);
        let mut shift = 0u32;
        for chunk in self.inner.iter() {
            if let Some(v) = chunk.get_value() {
                base += BigUint::from(v) << shift;
                shift += 64;
            } else {
                return None;
            }
        }

        Some(base)
    }
}

use cs_derive::*;

#[derive(Derivative, CSEqual, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct AsU128x2<E: Engine> {
    pub inner: [UInt128<E>; 2],
}

impl<E: Engine> From<&RegisterInputView<E>> for AsU128x2<E> {
    fn from(view: &RegisterInputView<E>) -> Self {
        Self {
            inner: view.u128x2_view.unwrap().clone(),
        }
    }
}

impl<E: Engine> From<Register<E>> for AsU128x2<E> {
    fn from(register: Register<E>) -> Self {
        Self {
            inner: register.inner,
        }
    }
}

impl<E: Engine> Into<Register<E>> for AsU128x2<E> {
    fn into(self) -> Register<E> {
        Register {
            inner: self.inner,
            is_ptr: Boolean::Constant(false),
        }
    }
}

impl<E: Engine> AsU128x2<E> {
    pub fn zero() -> Self {
        Self {
            inner: [UInt128::zero(); 2],
        }
    }

    #[track_caller]
    pub fn alloc_unchecked<CS>(cs: &mut CS, value: Option<BigUint>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let slices = split_some_into_fixed_number_of_limbs(value, 128, 2);
        let mut new = Self::zero();
        for i in 0..2 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            new.inner[i] = UInt128 { inner: allocated };
        }

        Ok(new)
    }

    #[track_caller]
    pub fn alloc_checked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        applies: Boolean,
        ctx: &mut OptimizationContext<E>,
        marker: CtxMarker,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 128, 2);
        let mut new = Self::zero();
        for i in 0..2 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            ctx.add_range_check(cs, &allocated, applies, marker, 128)?;
            new.inner[i] = UInt128 { inner: allocated };
        }

        Ok(new)
    }

    #[track_caller]
    pub fn alloc_pended<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        applies: Boolean,
        pended_ops: &mut PendingVec<E>,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 128, 2);
        let mut new = Self::zero();
        for i in 0..2 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            let pended_range_check = {
                (
                    PendingArithmeticRelation::RangeCheckRelation((allocated.clone(), 128)),
                    applies,
                )
            };
            pended_ops.push(pended_range_check);
            new.inner[i] = UInt128 { inner: allocated };
        }

        Ok(new)
    }

    #[track_caller]
    pub fn from_uint256<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        x: &UInt256<E>,
    ) -> Result<Self, SynthesisError> {
        let shifts = compute_shifts();
        let mut res = Self::zero();
        for (in_chunk, out) in x.inner.chunks(2).zip(res.inner.iter_mut()) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&in_chunk[0].inner, shifts[0]);
            lc.add_assign_number_with_coeff(&in_chunk[1].inner, shifts[64]);
            *out = UInt128::from_num_unchecked(lc.into_num(cs)?);
        }

        Ok(res)
    }

    #[track_caller]
    pub fn constant(value: BigUint) -> Self {
        let slices = split_into_fixed_number_of_limbs(value, 128, 2);
        let mut new = Self::zero();
        for (i, value) in slices.into_iter().enumerate() {
            let fe = biguint_to_fe::<E::Fr>(value);
            let constant = Num::Constant(fe);
            new.inner[i] = UInt128 { inner: constant };
        }

        new
    }

    pub fn get_value(&self) -> Option<BigUint> {
        let mut base = BigUint::from(0u64);
        let mut shift = 0u32;
        for chunk in self.inner.iter() {
            if let Some(v) = chunk.get_value() {
                base += BigUint::from(v) << shift;
                shift += 128;
            } else {
                return None;
            }
        }

        Some(base)
    }

    #[track_caller]
    pub fn conditionally_select<CS>(
        cs: &mut CS,
        flag: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut res = Self::zero();
        let iter = itertools::multizip((a.inner.iter(), b.inner.iter(), res.inner.iter_mut()));
        for (a_ch, b_ch, out_ch) in iter {
            *out_ch = UInt128::conditionally_select(cs, flag, &a_ch, &b_ch)?;
        }
        Ok(res)
    }

    #[track_caller]
    pub fn conditionally_replace<CS>(
        &mut self,
        cs: &mut CS,
        flag: &Boolean,
        replacement: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let new = Self::conditionally_select(cs, flag, replacement, &self)?;
        *self = new;
        Ok(())
    }

    #[track_caller]
    pub fn conditionally_enforce_equal<CS>(
        cs: &mut CS,
        flag: &Boolean,
        left: &Self,
        right: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        for (left_ch, right_ch) in left.inner.iter().zip(right.inner.iter()) {
            Num::conditionally_enforce_equal(cs, flag, &left_ch.inner, &right_ch.inner)?;
        }
        Ok(())
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
struct BothReprs<E: Engine> {
    pub as_u64x4: AsU64x4<E>,
    pub as_u128x2: AsU128x2<E>,
}

impl<E: Engine> From<&RegisterInputView<E>> for BothReprs<E> {
    fn from(view: &RegisterInputView<E>) -> Self {
        Self {
            as_u64x4: AsU64x4::from(view),
            as_u128x2: AsU128x2::from(view),
        }
    }
}

impl<E: Engine> Into<Register<E>> for BothReprs<E> {
    fn into(self) -> Register<E> {
        Register {
            inner: self.as_u128x2.inner,
            is_ptr: Boolean::constant(false),
        }
    }
}

impl<E: Engine> Into<RegisterInputView<E>> for BothReprs<E> {
    fn into(self) -> RegisterInputView<E> {
        RegisterInputView {
            u8x32_view: None,
            lowest160: None,
            u32x8_view: None,
            u64x4_view: Some(self.as_u64x4.inner),
            u128x2_view: Some(self.as_u128x2.inner),
            decomposed_lowest160: None,
            is_ptr: Boolean::constant(false),
        }
    }
}

impl<E: Engine> BothReprs<E> {
    pub fn zero() -> Self {
        Self {
            as_u64x4: AsU64x4::<E>::zero(),
            as_u128x2: AsU128x2::<E>::zero(),
        }
    }

    #[track_caller]
    pub fn alloc_unchecked<CS>(cs: &mut CS, value: Option<BigUint>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut as_u64x4 = AsU64x4::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            as_u64x4.inner[i] = UInt64 { inner: allocated };
        }

        let shifts = compute_shifts();
        let mut as_u128x2 = AsU128x2::zero();
        for (out, in_pair) in as_u128x2.inner.iter_mut().zip(as_u64x4.inner.chunks(2)) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&in_pair[0].inner, shifts[0]);
            lc.add_assign_number_with_coeff(&in_pair[1].inner, shifts[64]);
            *out = UInt128::from_num_unchecked(lc.into_num(cs)?);
        }

        Ok(BothReprs {
            as_u64x4,
            as_u128x2,
        })
    }

    #[track_caller]
    pub fn alloc_checked<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        applies: Boolean,
        ctx: &mut OptimizationContext<E>,
        marker: CtxMarker,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut as_u64x4 = AsU64x4::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            ctx.add_range_check(cs, &allocated, applies, marker, 64)?;
            as_u64x4.inner[i] = UInt64 { inner: allocated };
        }

        let shifts = compute_shifts();
        let mut as_u128x2 = AsU128x2::zero();
        for (out, in_pair) in as_u128x2.inner.iter_mut().zip(as_u64x4.inner.chunks(2)) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&in_pair[0].inner, shifts[0]);
            lc.add_assign_number_with_coeff(&in_pair[1].inner, shifts[64]);
            *out = UInt128::from_num_unchecked(lc.into_num(cs)?);
        }

        Ok(BothReprs {
            as_u64x4,
            as_u128x2,
        })
    }

    #[track_caller]
    pub fn alloc_pended<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<BigUint>,
        applies: Boolean,
        pended_ops: &mut PendingVec<E>,
    ) -> Result<Self, SynthesisError> {
        let slices = split_some_into_fixed_number_of_limbs(value, 64, 4);
        let mut as_u64x4 = AsU64x4::zero();
        for i in 0..4 {
            let fe = some_biguint_to_fe::<E::Fr>(&slices[i]);
            let allocated = Num::Variable(AllocatedNum::alloc(cs, || Ok(*fe.get()?))?);
            let pended_range_check = {
                (
                    PendingArithmeticRelation::RangeCheckRelation((allocated.clone(), 64)),
                    applies,
                )
            };
            pended_ops.push(pended_range_check);
            as_u64x4.inner[i] = UInt64 { inner: allocated };
        }

        let shifts = compute_shifts();
        let mut as_u128x2 = AsU128x2::zero();
        for (out, in_pair) in as_u128x2.inner.iter_mut().zip(as_u64x4.inner.chunks(2)) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&in_pair[0].inner, shifts[0]);
            lc.add_assign_number_with_coeff(&in_pair[1].inner, shifts[64]);
            *out = UInt128::from_num_unchecked(lc.into_num(cs)?);
        }

        Ok(BothReprs {
            as_u64x4,
            as_u128x2,
        })
    }
}

fn select_u128x2_candidates<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    flags: &[Boolean],
    candidates: &[AsU128x2<E>],
) -> Result<AsU128x2<E>, SynthesisError> {
    let mut val = candidates[0].clone();
    for (flag, candidate) in flags[1..].iter().zip(candidates[1..].iter()) {
        val = AsU128x2::conditionally_select(cs, flag, candidate, &val)?;
    }

    Ok(val)
}

fn select_u64x4_candidates<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    flags: &[Boolean],
    candidates: &[AsU64x4<E>],
) -> Result<AsU64x4<E>, SynthesisError> {
    let mut val = candidates[0].clone();
    for (flag, candidate) in flags[1..].iter().zip(candidates[1..].iter()) {
        val = AsU64x4::conditionally_select(cs, flag, candidate, &val)?;
    }

    Ok(val)
}

/// Describes an optimization request in a form a + b = c + of_bit,
/// that can be reordered to subtraction with borrow
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct AddSubRelationship<E: Engine> {
    pub a: AsU128x2<E>,
    pub b: AsU128x2<E>,
    pub c: AsU128x2<E>,
    pub of_bit: Boolean,
}

impl<E: Engine> AddSubRelationship<E> {
    pub fn new(a: AsU128x2<E>, b: AsU128x2<E>, c: AsU128x2<E>, of_bit: Boolean) -> Self {
        AddSubRelationship { a, b, c, of_bit }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct MulDivRelationship<E: Engine> {
    pub a: AsU64x4<E>,
    pub b: AsU64x4<E>,
    pub remainder: AsU128x2<E>,
    pub high: AsU128x2<E>,
    pub low: AsU128x2<E>,
}

impl<E: Engine> MulDivRelationship<E> {
    pub fn new(
        a: AsU64x4<E>,
        b: AsU64x4<E>,
        remainder: AsU128x2<E>,
        high: AsU128x2<E>,
        low: AsU128x2<E>,
    ) -> Self {
        MulDivRelationship {
            a,
            b,
            remainder,
            high,
            low,
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct ZeroCheckRelationship<E: Engine> {
    pub is_not_zero: Boolean,
    pub value: AsU128x2<E>,
}

impl<E: Engine> ZeroCheckRelationship<E> {
    pub fn new(value: AsU128x2<E>, is_not_zero: Boolean) -> Self {
        ZeroCheckRelationship { is_not_zero, value }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct RangeCheckRelation<E: Engine> {
    pub width: usize,
    pub value: Num<E>,
}

impl<E: Engine> RangeCheckRelation<E> {
    pub fn new(value: Num<E>, width: usize) -> Self {
        RangeCheckRelation { width, value }
    }
}

pub struct OnceExecHelper<E: Engine> {
    pub once_lambdas: HashMap<usize, Box<dyn Any>>,
    pub _marker: std::marker::PhantomData<E>,
}

impl<E: Engine> OnceExecHelper<E> {
    pub fn new() -> Self {
        OnceExecHelper {
            once_lambdas: HashMap::new(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn execute_once<CS, F>(
        &mut self,
        cs: &mut CS,
        marker: usize,
        lambda: F,
    ) -> Result<&Box<dyn Any>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce(&mut CS) -> Result<Box<dyn Any>, SynthesisError>,
    {
        let res = match self.once_lambdas.entry(marker) {
            Entry::Occupied(e) => &*e.into_mut(),
            Entry::Vacant(e) => {
                let inner = lambda(cs)?;
                &*e.insert(inner)
            }
        };
        Ok(res)
    }
}

pub struct OptimizationContext<E: Engine> {
    pub range_checks_queue: Vec<(CtxMarker, Boolean, RangeCheckRelation<E>)>,
    pub unconditional_range_checks: Vec<(usize, Num<E>)>,
    pub uint256_divmul_tuples: Vec<(CtxMarker, Boolean, MulDivRelationship<E>)>,
    pub uint256_addsub_tuples: Vec<(CtxMarker, Boolean, AddSubRelationship<E>)>,
    pub zero_checks_tuples: Vec<(CtxMarker, Boolean, ZeroCheckRelationship<E>)>,
    // pub uint256_register_update_queue: [Vec<(CtxMarker, Boolean, Register<E>)>; MAX_DST_UINT256_REGISTERS_PER_OP],
    // pub execute_opcode_map: OpcodeMap<E>,
    pub once_exec_helper: OnceExecHelper<E>,
    pub boolean_constraints_queue: Vec<AllocatedNum<E>>,
}

impl<E: Engine> OptimizationContext<E> {
    // pub fn new_from_opcode<CS: ConstraintSystem<E>>(
    //     _cs: &mut CS, opcode_map: OpcodeMap<E>
    // ) -> Result<Self, SynthesisError>
    // {
    //     let ctx = Self {
    //         range_checks_queue: vec![],
    //         unconditional_range_checks: vec![],
    //         uint256_divmul_tuples: vec![],
    //         uint256_addsub_tuples: vec![],
    //         zero_checks_tuples: vec![],
    //         uint256_register_update_queue: Default::default(),
    //         execute_opcode_map: opcode_map,
    //         once_exec_helper: OnceExecHelper::<E>::new(),
    //         boolean_constraints_queue: vec![],
    //     };

    //     Ok(ctx)
    // }

    pub fn empty() -> Self {
        let ctx = Self {
            range_checks_queue: vec![],
            unconditional_range_checks: vec![],
            uint256_divmul_tuples: vec![],
            uint256_addsub_tuples: vec![],
            zero_checks_tuples: vec![],
            // uint256_register_update_queue: Default::default(),
            // execute_opcode_map: OpcodeMap::<E> {
            //     opcode: UInt8::<E>::zero(),
            //     inner_map: HashMap::<&'static str, Boolean>::new(),
            // },
            once_exec_helper: OnceExecHelper::<E>::new(),
            boolean_constraints_queue: vec![],
        };

        ctx
    }

    fn make_witness_for_addition(
        a: &AsU128x2<E>,
        b: &AsU128x2<E>,
    ) -> (Option<BigUint>, Option<bool>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                let result = a + b;
                let c = result.clone() % (BigUint::from(1u64) << 256);
                use num_traits::identities::Zero;
                let of = !((result >> 256u32).is_zero());
                (Some(c), Some(of))
            }
            _ => (None, None),
        }
    }

    fn make_witness_for_subtraction(
        a: &AsU128x2<E>,
        b: &AsU128x2<E>,
    ) -> (Option<BigUint>, Option<bool>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                let borrow = &a < &b;
                let mut result = BigUint::from(0u64);
                if borrow {
                    result += BigUint::from(1u64) << 256u32;
                }
                result += a;
                result -= b;
                (Some(result), Some(borrow))
            }
            _ => (None, None),
        }
    }

    fn make_witness_for_multiplication(
        a: &AsU64x4<E>,
        b: &AsU64x4<E>,
    ) -> (Option<BigUint>, Option<BigUint>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                let result = a * b;
                let low = result.clone() % (BigUint::from(1u64) << 256);
                let high = result >> 256u32;
                (Some(high), Some(low))
            }
            _ => (None, None),
        }
    }

    fn make_witness_for_division(
        a: &AsU128x2<E>,
        b: &AsU64x4<E>,
    ) -> (Option<BigUint>, Option<BigUint>) {
        match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                use num_traits::Zero;
                if b.is_zero() {
                    (Some(BigUint::from(0u64)), Some(a))
                } else {
                    use num_integer::Integer;
                    let (q, r) = a.div_rem(&b);
                    (Some(q), Some(r))
                }
            }
            _ => (None, None),
        }
    }

    #[track_caller]
    pub fn add_zero_check<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        reg: &Register<E>,
        applies: Boolean,
        marker: CtxMarker,
    ) -> Result<Boolean, SynthesisError> {
        use num_traits::Zero;
        let is_not_zero_witness = reg.get_value().map(|x| !x.is_zero());
        let res_flag = self.allocate_boolean(cs, is_not_zero_witness)?;

        let val = AsU128x2 {
            inner: reg.inner.clone(),
        };
        let relation = ZeroCheckRelationship::new(val, res_flag);
        self.zero_checks_tuples.push((marker, applies, relation));

        Ok(res_flag.not())
    }

    #[track_caller]
    pub fn append_num_to_register_convesion<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        num: &Num<E>,
        applies: Boolean,
        marker: CtxMarker,
    ) -> Result<Register<E>, SynthesisError> {
        let witness = num.get_value().map(|x| fe_to_biguint(&x));
        let reg = AsU128x2::alloc_checked(cs, witness, applies.clone(), self, marker)?;

        let mut char_as_biguint = BigUint::from(0u64);
        for limb in E::Fr::char().as_ref().iter().rev() {
            char_as_biguint <<= 64;
            char_as_biguint += BigUint::from(*limb);
        }
        char_as_biguint -= BigUint::from(1u64);
        let char_as_u256 = AsU128x2::constant(char_as_biguint);

        let (no_of_witness, _of_witness) = Self::make_witness_for_subtraction(&char_as_u256, &reg);
        // no range check here as optimizer takes care of it
        let no_of = AsU128x2::alloc_checked(cs, no_of_witness, applies.clone(), self, marker)?;
        let new_of = Boolean::constant(false);

        let relation = AddSubRelationship::new(no_of, reg.clone(), char_as_u256, new_of);
        self.uint256_addsub_tuples.push((marker, applies, relation));

        Ok(reg.into())
    }

    #[track_caller]
    pub fn add_addition_relation<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        a_view: &RegisterInputView<E>,
        b_view: &RegisterInputView<E>,
        applies: Boolean,
        marker: CtxMarker,
    ) -> Result<(Register<E>, Boolean), SynthesisError> {
        let a = AsU128x2::from(a_view);
        let b = AsU128x2::from(b_view);

        let (result_witness, of_witness) = Self::make_witness_for_addition(&a, &b);
        let result = AsU128x2::alloc_checked(cs, result_witness, applies.clone(), self, marker)?;
        let new_of = self.allocate_boolean(cs, of_witness)?;

        let relation = AddSubRelationship::new(a.clone(), b.clone(), result.clone(), new_of);
        self.uint256_addsub_tuples.push((marker, applies, relation));
        Ok((result.into(), new_of))
    }

    #[track_caller]
    pub fn add_pending_addition_relation<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        a_view: &RegisterInputView<E>,
        b_view: &RegisterInputView<E>,
        applies: Boolean,
        pended_ops: &mut PendingVec<E>,
    ) -> Result<(Register<E>, Boolean), SynthesisError> {
        // println!("Adding pending ops");
        // dbg!(applies.get_value());
        let a = AsU128x2::from(a_view);
        let b = AsU128x2::from(b_view);
        let (result_witness, of_witness) = Self::make_witness_for_addition(&a, &b);

        let result = AsU128x2::alloc_pended(cs, result_witness, applies.clone(), pended_ops)?;
        let new_of = self.allocate_boolean(cs, of_witness)?;

        let relation = AddSubRelationship::new(a.clone(), b.clone(), result.clone(), new_of);
        let pended_addition = (PendingArithmeticRelation::AddSubRelation(relation), applies);
        pended_ops.push(pended_addition);

        Ok((result.into(), new_of))
    }

    #[track_caller]
    pub fn add_subtraction_relation<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        base_view: &RegisterInputView<E>,
        to_sub_view: &RegisterInputView<E>,
        applies: Boolean,
        marker: CtxMarker,
    ) -> Result<(Register<E>, Boolean), SynthesisError> {
        // dbg!(&marker);
        // dbg!(applies.get_value());
        // dbg!(self.uint256_addsub_tuples.len());

        let base = AsU128x2::from(base_view);
        let to_sub = AsU128x2::from(to_sub_view);

        let (result_witness, borrow_witness) = Self::make_witness_for_subtraction(&base, &to_sub);
        let result = AsU128x2::alloc_checked(cs, result_witness, applies.clone(), self, marker)?;
        let new_borrow = self.allocate_boolean(cs, borrow_witness)?;

        // base - sub + borrow = result
        // result + sub = base + borrow
        let relation =
            AddSubRelationship::new(result.clone(), to_sub.clone(), base.clone(), new_borrow);
        self.uint256_addsub_tuples.push((marker, applies, relation));
        Ok((result.into(), new_borrow))
    }

    #[track_caller]
    pub fn add_mul_relation<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        a_view: &RegisterInputView<E>,
        b_view: &RegisterInputView<E>,
        applies: Boolean,
        marker: CtxMarker,
    ) -> Result<(RegisterInputView<E>, RegisterInputView<E>), SynthesisError> {
        let a = AsU64x4::from(a_view);
        let b = AsU64x4::from(b_view);

        let (witness_high, witness_low) = Self::make_witness_for_multiplication(&a, &b);
        let high = BothReprs::alloc_checked(cs, witness_high, applies.clone(), self, marker)?;
        let low = BothReprs::alloc_checked(cs, witness_low, applies.clone(), self, marker)?;

        let relation = MulDivRelationship::new(
            a,
            b,
            AsU128x2::zero(),
            high.as_u128x2.clone(),
            low.as_u128x2.clone(),
        );
        self.uint256_divmul_tuples.push((marker, applies, relation));

        Ok((low.into(), high.into()))
    }

    #[track_caller]
    pub fn add_pending_mul_relation<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        a_view: &RegisterInputView<E>,
        b_view: &RegisterInputView<E>,
        applies: Boolean,
        pended_ops: &mut PendingVec<E>,
    ) -> Result<(RegisterInputView<E>, RegisterInputView<E>), SynthesisError> {
        let a = AsU64x4::from(a_view);
        let b = AsU64x4::from(b_view);

        let (witness_high, witness_low) = Self::make_witness_for_multiplication(&a, &b);
        let high = BothReprs::alloc_pended(cs, witness_high, applies.clone(), pended_ops)?;
        let low = BothReprs::alloc_pended(cs, witness_low, applies.clone(), pended_ops)?;

        let relation = MulDivRelationship::new(
            a,
            b,
            AsU128x2::zero(),
            high.as_u128x2.clone(),
            low.as_u128x2.clone(),
        );
        let pended_mul = (PendingArithmeticRelation::MulDivRelation(relation), applies);
        pended_ops.push(pended_mul);

        Ok((low.into(), high.into()))
    }

    #[track_caller]
    pub fn add_div_relation<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        dividend_view: &RegisterInputView<E>,
        divisor_view: &RegisterInputView<E>,
        applies: Boolean,
        marker: CtxMarker,
    ) -> Result<(RegisterInputView<E>, RegisterInputView<E>), SynthesisError> {
        let dividend = AsU128x2::from(dividend_view);
        let divisor = AsU64x4::from(divisor_view);

        let (witness_quotient, witness_remainder) =
            Self::make_witness_for_division(&dividend, &divisor);
        let quotient =
            BothReprs::alloc_checked(cs, witness_quotient, applies.clone(), self, marker)?;
        let remainder =
            BothReprs::alloc_checked(cs, witness_remainder, applies.clone(), self, marker)?;

        // a, b, high, low, remaider
        // for a relationship like a*b + remainder = 2^256 * high + low
        // and here we have for a/b = q and a%b = r
        // q*m + r = 2^256 * 0 + input
        let relation = MulDivRelationship::new(
            divisor,
            quotient.as_u64x4.clone(),
            remainder.as_u128x2.clone(),
            AsU128x2::zero(),
            dividend,
        );
        self.uint256_divmul_tuples.push((marker, applies, relation));
        Ok((quotient.into(), remainder.into()))
    }

    #[track_caller]
    pub fn add_pending_div_relation<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        dividend_view: &RegisterInputView<E>,
        divisor_view: &RegisterInputView<E>,
        applies: Boolean,
        pended_ops: &mut PendingVec<E>,
    ) -> Result<(RegisterInputView<E>, RegisterInputView<E>), SynthesisError> {
        let dividend = AsU128x2::from(dividend_view);
        let divisor = AsU64x4::from(divisor_view);

        let (witness_quotient, witness_remainder) =
            Self::make_witness_for_division(&dividend, &divisor);
        let quotient = BothReprs::alloc_pended(cs, witness_quotient, applies.clone(), pended_ops)?;
        let remainder =
            BothReprs::alloc_pended(cs, witness_remainder, applies.clone(), pended_ops)?;

        // a, b, high, low, remaider
        // for a relationship like a*b + remainder = 2^256 * high + low
        // and here we have for a/b = q and a%b = r
        // q*m + r = 2^256 * 0 + input
        let relation = MulDivRelationship::new(
            divisor,
            quotient.as_u64x4.clone(),
            remainder.as_u128x2.clone(),
            AsU128x2::zero(),
            dividend,
        );
        let pended_div = (PendingArithmeticRelation::MulDivRelation(relation), applies);
        pended_ops.push(pended_div);

        Ok((quotient.into(), remainder.into()))
    }

    // #[track_caller]
    // pub fn add_register_update(&mut self, value: Register<E>, applies: Boolean, index: usize, marker: CtxMarker) {
    //     self.uint256_register_update_queue[index].push((marker, applies, value));
    // }

    #[track_caller]
    pub fn add_range_check<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        for_element: &Num<E>,
        applies: Boolean,
        marker: CtxMarker,
        width: usize,
    ) -> Result<(), SynthesisError> {
        assert!(width <= E::Fr::CAPACITY as usize);
        match (for_element.get_value(), applies.get_value()) {
            (Some(val), Some(_applies)) => {
                assert!(val.into_repr().num_bits() as usize <= width);
            }
            _ => {}
        }

        if width <= VM_RANGE_CHECK_TABLE_WIDTH {
            // it's easier to just constraint and do not select
            self.add_unconditional_range_check(for_element, marker, width);
            return Ok(());
        }

        if width <= RANGE_CHECK_THRESHOLD {
            let relation = RangeCheckRelation::new(*for_element, width);
            self.range_checks_queue.push((marker, applies, relation));
            return Ok(());
        }

        // split into variables of new length and enforce decomposition
        assert_eq!(for_element.is_constant(), false);
        let num_of_chunks = (width + RANGE_CHECK_THRESHOLD - 1) / RANGE_CHECK_THRESHOLD;
        let value = for_element.get_value();
        let witness_chunks = split_some_into_slices(value, RANGE_CHECK_THRESHOLD, num_of_chunks);

        let mut chunks = Vec::with_capacity(witness_chunks.len());
        let has_remainder = num_of_chunks * RANGE_CHECK_THRESHOLD != width;
        let last_chunk_width = if has_remainder {
            width % RANGE_CHECK_THRESHOLD
        } else {
            RANGE_CHECK_THRESHOLD
        };

        for (_, is_last, wit) in witness_chunks.iter().identify_first_last() {
            let allocated_num = AllocatedNum::alloc(cs, || wit.grab())?;
            let num = Num::Variable(allocated_num);
            if is_last && (last_chunk_width <= VM_RANGE_CHECK_TABLE_WIDTH) {
                self.add_unconditional_range_check(&num, marker, last_chunk_width);
            } else {
                let relation = RangeCheckRelation::new(num.clone(), RANGE_CHECK_THRESHOLD);
                self.range_checks_queue.push((marker, applies, relation));
            }
            chunks.push(num);
        }

        let shifts = compute_shifts();
        let mut offset = 0;
        let mut lc = LinearCombination::zero();
        for chunk in chunks.iter() {
            lc.add_assign_number_with_coeff(&chunk, shifts[offset]);
            offset += RANGE_CHECK_THRESHOLD;
        }
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        lc.add_assign_number_with_coeff(&for_element, minus_one);
        lc.enforce_zero(cs)
    }

    #[track_caller]
    pub fn add_unconditional_range_check(
        &mut self,
        for_element: &Num<E>,
        _marker: CtxMarker,
        width: usize,
    ) {
        self.unconditional_range_checks.push((width, *for_element));
    }

    // #[track_caller]
    // pub fn output_destination_updates<CS: ConstraintSystem<E>>(
    //     &mut self, cs: &mut CS
    // ) -> Result<([(Boolean, Register<E>); MAX_DST_UINT256_REGISTERS_PER_OP]), SynthesisError> {
    //     let mut result : [(Boolean, Register<E>); MAX_DST_UINT256_REGISTERS_PER_OP] = Default::default();

    //     // for each possible dst position select a candidate
    //     for index in 0..MAX_DST_UINT256_REGISTERS_PER_OP {
    //         // walk over the scheduled updates for this index
    //         // flags if this change applies by the opcode
    //         let len = self.uint256_register_update_queue[index].len();
    //         let mut markers = Vec::<CtxMarker>::with_capacity(len);
    //         let mut applicability_flags = Vec::<Boolean>::with_capacity(len);
    //         let mut candidate_values = Vec::<Register<E>>::with_capacity(len);

    //         for (marker, flag, val) in self.uint256_register_update_queue[index].drain(..) {
    //             markers.push(marker);
    //             applicability_flags.push(flag);
    //             candidate_values.push(val)
    //         };

    //         Self::assert_orthigonality(&markers, &applicability_flags);

    //         // do the partitioning
    //         let global_applciability = smart_or(cs, &applicability_flags[..])?;
    //         // we are ok to just multiselect here, because all the opcodes are executed disjointly
    //         let value = Register::unsafe_multiselection_using_linear_combination(
    //             cs, &applicability_flags[..], &candidate_values[..])?;

    //         result[index] = (global_applciability, value);
    //     }

    //     Ok(result)
    // }

    #[track_caller]
    pub fn enforce_addsub_algebraic_relationships<CS>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut elem_vec = std::mem::replace(&mut self.uint256_addsub_tuples, vec![]);
        while elem_vec.len() > 0 {
            let (current, remaining) = partition_dedup_by_key(elem_vec, |x| x.0);
            let len = current.len();
            let mut markers = Vec::<CtxMarker>::with_capacity(len);
            let mut applicability_flags = Vec::<Boolean>::with_capacity(len);
            let mut a_candidate_values = Vec::<AsU128x2<E>>::with_capacity(len);
            let mut b_candidate_values = Vec::<AsU128x2<E>>::with_capacity(len);
            let mut c_candidate_values = Vec::<AsU128x2<E>>::with_capacity(len);
            let mut of_candidate_values = Vec::<Boolean>::with_capacity(len);

            for (marker, flag, relation) in current.iter().cloned() {
                markers.push(marker);
                applicability_flags.push(flag);
                // dbg!(marker);
                // dbg!(flag.get_value());
                a_candidate_values.push(relation.a);
                b_candidate_values.push(relation.b);
                c_candidate_values.push(relation.c);
                of_candidate_values.push(relation.of_bit);
            }
            assert!(has_unique_elements(markers.iter()));
            assert!(
                applicability_flags
                    .iter()
                    .filter(|x| x.get_value().unwrap_or(false))
                    .count()
                    <= 1
            );

            // we are ok to just multiselect here, because all the opcodes are executed disjointly
            let a = select_u128x2_candidates(cs, &applicability_flags, &a_candidate_values)?;

            let b = select_u128x2_candidates(cs, &applicability_flags, &b_candidate_values)?;

            let c = select_u128x2_candidates(cs, &applicability_flags, &c_candidate_values)?;

            let mut final_of_flag = of_candidate_values[0];
            for (flag, candidate) in applicability_flags[1..]
                .iter()
                .zip(of_candidate_values[1..].iter())
            {
                final_of_flag = Boolean::conditionally_select(cs, flag, candidate, &final_of_flag)?;
            }

            let intermediate_of_witness = match (a.get_value(), b.get_value()) {
                (Some(a), Some(b)) => {
                    let modulus = BigUint::from(1u64) << 128u32;
                    let of = ((a % &modulus) + (b % &modulus)) >> 128u8;

                    use num_traits::Zero;
                    Some(!of.is_zero())
                }
                _ => None,
            };
            let intermediate_of = self.allocate_boolean(cs, intermediate_of_witness)?;

            let shifts = compute_shifts::<E::Fr>();
            let mut minus_one = E::Fr::one();
            minus_one.negate();

            let word_shift = shifts[128].clone();
            let mut minus_word_shift = word_shift;
            minus_word_shift.negate();

            // enforce the relationship
            let mut lc_low = LinearCombination::zero();
            lc_low.add_assign_number_with_coeff(&a.inner[0].inner, E::Fr::one());
            lc_low.add_assign_number_with_coeff(&b.inner[0].inner, E::Fr::one());
            lc_low.add_assign_number_with_coeff(&c.inner[0].inner, minus_one);
            lc_low.add_assign_boolean_with_coeff(&intermediate_of, minus_word_shift);
            lc_low.enforce_zero(cs)?;

            let mut lc_high = LinearCombination::zero();
            lc_high.add_assign_number_with_coeff(&a.inner[1].inner, E::Fr::one());
            lc_high.add_assign_number_with_coeff(&b.inner[1].inner, E::Fr::one());
            lc_high.add_assign_number_with_coeff(&c.inner[1].inner, minus_one);
            lc_high.add_assign_boolean_with_coeff(&intermediate_of, E::Fr::one());
            lc_high.add_assign_boolean_with_coeff(&final_of_flag, minus_word_shift);
            lc_high.enforce_zero(cs)?;

            elem_vec = remaining;
        }

        Ok(())
    }

    #[track_caller]
    pub fn enforce_divmul_algebraic_relationships<CS>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        use crate::bellman::plonk::better_better_cs::cs::{
            ArithmeticTerm, Gate, MainGate, MainGateTerm,
        };
        let dummy_marker = CtxMarker::dummy_marker();

        let mut elem_vec = std::mem::replace(&mut self.uint256_divmul_tuples, vec![]);

        while elem_vec.len() > 0 {
            let (current, remaining) = partition_dedup_by_key(elem_vec, |x| x.0);
            let len = current.len();
            let mut markers = Vec::<CtxMarker>::with_capacity(len);
            let mut applicability_flags = Vec::<Boolean>::with_capacity(len);
            let mut a_candidate_values = Vec::<AsU64x4<E>>::with_capacity(len);
            let mut b_candidate_values = Vec::<AsU64x4<E>>::with_capacity(len);
            let mut rem_candidate_values = Vec::<AsU128x2<E>>::with_capacity(len);
            let mut res_low_candidate_values = Vec::<AsU128x2<E>>::with_capacity(len);
            let mut res_high_candidate_values = Vec::<AsU128x2<E>>::with_capacity(len);

            for (marker, flag, relation) in current.iter().cloned() {
                markers.push(marker);
                applicability_flags.push(flag);
                a_candidate_values.push(relation.a);
                b_candidate_values.push(relation.b);
                rem_candidate_values.push(relation.remainder);
                res_low_candidate_values.push(relation.low);
                res_high_candidate_values.push(relation.high)
            }

            Self::assert_orthigonality(&markers, &applicability_flags);

            // we are ok to just multiselect here, because all the opcodes are executed disjointly
            let a = select_u64x4_candidates(cs, &applicability_flags, &a_candidate_values)?;
            let b = select_u64x4_candidates(cs, &applicability_flags, &b_candidate_values)?;
            let remainder =
                select_u128x2_candidates(cs, &applicability_flags, &rem_candidate_values)?;
            let low =
                select_u128x2_candidates(cs, &applicability_flags, &res_low_candidate_values)?;
            let high =
                select_u128x2_candidates(cs, &applicability_flags, &res_high_candidate_values)?;

            // low[0] + carry_out = a[0] * b[0] + a[1] * b[0] + a[0] * b[1] + rem[0]
            // carry_out is at most 66-bits long
            // low[1] + carry_out = a[1] * b[1] + a[0] * b[2] + a[2] * b[0] + a[3] * b[0] + a[2] * b[1] +
            // a[1] * b[2] + a[0] * b[3] + rem[1] + carry_in
            // and so on...
            const NUM_LIMBS_IN_MULTIPLIERS: usize = 4;
            let shifts = compute_shifts::<E::Fr>();
            let mut minus_one = E::Fr::one();
            minus_one.negate();

            let word_shift = shifts[64].clone();
            let two_words_shift = shifts[128].clone();
            let two_words_shift_right = two_words_shift.inverse().unwrap();

            let mut input_carry = Num::zero();
            let mul_limbs = low.inner.into_iter().chain(high.inner.into_iter());

            for (k, mul_res_limb) in mul_limbs.enumerate() {
                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&input_carry, E::Fr::one());

                // add terms like a[i] * b[j], where i+j = 2*k
                for i in 0..2 * k + 1 {
                    let j = 2 * k - i;

                    if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {
                        let mul_term = a.inner[i].inner.mul(cs, &b.inner[j].inner)?;
                        lc.add_assign_number_with_coeff(&mul_term, E::Fr::one());
                    }
                }

                // add terms like a[i] * b[j], where i+j = 2*k+1
                for i in 0..(2 * k + 2) {
                    let j = 2 * k + 1 - i;

                    if (i < NUM_LIMBS_IN_MULTIPLIERS) && (j < NUM_LIMBS_IN_MULTIPLIERS) {
                        let mul_term = a.inner[i].inner.mul(cs, &b.inner[j].inner)?;
                        lc.add_assign_number_with_coeff(&mul_term, word_shift.clone());
                    }
                }

                // add remainder
                if k < 2 {
                    lc.add_assign_number_with_coeff(&remainder.inner[k].inner, E::Fr::one());
                }

                lc.add_assign_number_with_coeff(&mul_res_limb.inner, minus_one.clone());
                lc.scale(&two_words_shift_right);

                if k != 3 {
                    // our inputs and output into this long addition relation
                    // are of the fixed width, so let's consider a linear combination like
                    // a[0] * b[0] + a[1] * b[0] * 2^64 + a[0] * b[1] *2^64 - low[0] -
                    // low[1] * 2^64 + remainder[0] + remainder[1] * 2^64 = tmp
                    // a malicious prover could e.g. place invalid low[1],
                    // so tmp would be < 0 or not contain 128 zero lowest bits,
                    // so we always need a range check here
                    input_carry = lc.into_num(cs)?;
                    self.add_unconditional_range_check(&input_carry, dummy_marker, 64 + 8);
                } else {
                    lc.enforce_zero(cs)?;
                }
            }
            elem_vec = remaining;
        }

        Ok(())
    }

    pub fn enforce_zero_checks<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut elem_vec = std::mem::replace(&mut self.zero_checks_tuples, vec![]);

        while elem_vec.len() > 0 {
            let (current, remaining) = partition_dedup_by_key(elem_vec, |x| x.0);
            let len = current.len();

            let mut markers = Vec::<CtxMarker>::with_capacity(len);
            let mut applicability_flags = Vec::<Boolean>::with_capacity(len);
            let mut candidates = Vec::<AsU128x2<E>>::with_capacity(len);
            let mut not_zero_flags = Vec::<Boolean>::with_capacity(len);

            for (marker, flag, relation) in current.iter().cloned() {
                markers.push(marker);
                applicability_flags.push(flag);
                candidates.push(relation.value);
                not_zero_flags.push(relation.is_not_zero);
            }

            Self::assert_orthigonality(&markers, &applicability_flags);

            // we are ok to just multiselect here, because all the opcodes are executed disjointly,

            // let val = AsU128x2::unsafe_multiselection_using_linear_combination(
            //     cs, &applicability_flags[..], &candidates[..]
            // )?;

            let mut val = candidates[0].clone();
            for (flag, candidate) in applicability_flags[1..].iter().zip(candidates[1..].iter()) {
                val = AsU128x2::conditionally_select(cs, flag, candidate, &val)?;
            }

            let mut is_not_zero = not_zero_flags[0];
            for (flag, candidate) in applicability_flags[1..]
                .iter()
                .zip(not_zero_flags[1..].iter())
            {
                is_not_zero = Boolean::conditionally_select(cs, flag, candidate, &is_not_zero)?;
            }

            // let is_not_zero = UncheckedBoolean::unsafe_multiselection_using_linear_combination(
            //     cs, &applicability_flags[..], &not_zero_flags[..]
            // )?;

            let is_zero_0 = val.inner[0].inner.is_zero(cs)?;
            let is_zero_1 = val.inner[1].inner.is_zero(cs)?;

            let is_zero_0_num = Num::<E>::from_boolean_is(is_zero_0);
            let is_zero_1_num = Num::<E>::from_boolean_is(is_zero_1);

            // full_zero = is_zero_0 AND is_zero_1
            // is_not_zero = !full_zero = 1 - full_zero

            // 1 - is_not_zero  = is_zero_0 * is_zero_1
            let mul_term =
                ArithmeticTerm::from_variable(is_zero_0_num.get_variable().get_variable())
                    .mul_by_variable(is_zero_1_num.get_variable().get_variable());
            let flag_as_num = Num::<E>::from_boolean_is(is_not_zero); // guarantee that we do not need any forms of negation
            let other_term =
                ArithmeticTerm::from_variable(flag_as_num.get_variable().get_variable());
            let mut gate = MainGateTerm::new();
            let cnst_term = ArithmeticTerm::constant(E::Fr::one());
            // is_zero_0 * is_zero_1 + is_not_zero - 1 == 0
            gate.add_assign(mul_term);
            gate.add_assign(other_term);
            gate.sub_assign(cnst_term);
            cs.allocate_main_gate(gate)?;

            // let is_not_zero_checked = smart_or(cs, &[is_zero_0.not(), is_zero_1.not()])?;
            // Boolean::enforce_equal(cs, &is_not_zero_checked, &is_not_zero)?;

            // // to enforce that check is zero, two constraints are required:
            // // val * flag = 0;
            // // val * inv = 1 - flag
            // // Note, that there is no need to enforce booleanity of flag itself
            // let mut chunk_flags = [Num::<E>::zero(); 2];
            // for (flag_out, limb) in chunk_flags.iter_mut().zip(val.inner.iter()) {
            //     let inv = AllocatedNum::alloc(cs, || limb.inner.get_value().map(|x| {
            //         x.inverse().unwrap_or(E::Fr::zero())
            //     }).grab())?;

            //     let flag = AllocatedNum::alloc(cs, || limb.inner.get_value().map(|x| {
            //         if x.is_zero() { E::Fr::one() } else { E::Fr::zero() }
            //     }).grab())?;

            //     let inv_var = inv.get_variable();
            //     let flag_var = flag.get_variable();
            //     let val_var = limb.inner.get_variable().get_variable();

            //     // val * flag = 0;
            //     let mul_term = ArithmeticTerm::from_variable(val_var).mul_by_variable(flag_var);
            //     let mut gate = MainGateTerm::new();
            //     gate.add_assign(mul_term);
            //     cs.allocate_main_gate(gate)?;

            //     // val * inv  + flag - 1 = 0;
            //     let mul_term = ArithmeticTerm::from_variable(val_var).mul_by_variable(inv_var);
            //     let cnst_term = ArithmeticTerm::constant(E::Fr::one());
            //     let add_term = ArithmeticTerm::from_variable(flag_var);
            //     let mut gate = MainGateTerm::new();
            //     gate.add_assign(mul_term);
            //     gate.add_assign(add_term);
            //     gate.sub_assign(cnst_term);
            //     cs.allocate_main_gate(gate)?;

            //     *flag_out = Num::Variable(flag);
            // }

            // // 1 - is_not_zero  = flag_chunk0 * flag_chunk1
            // let mul_term = ArithmeticTerm::from_variable(
            //     chunk_flags[0].get_variable().get_variable()).mul_by_variable(
            //     chunk_flags[1].get_variable().get_variable()
            // );
            // let flag_as_num = Num::<E>::from_boolean_is(is_not_zero); // guarantee that we do not need any forms of negation
            // let other_term = ArithmeticTerm::from_variable(flag_as_num.get_variable().get_variable());
            // let mut gate = MainGateTerm::new();
            // let cnst_term = ArithmeticTerm::constant(E::Fr::one());
            // gate.sub_assign(cnst_term);
            // gate.add_assign(mul_term);
            // gate.add_assign(other_term);
            // cs.allocate_main_gate(gate)?;

            elem_vec = remaining;
        }

        Ok(())
    }

    pub fn enforce_unconditional_range_checks<CS>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let shifts = compute_shifts::<E::Fr>();
        for (width, num) in self.unconditional_range_checks.drain(..) {
            let shift_idx = width % VM_RANGE_CHECK_TABLE_WIDTH;
            let new_width = next_multiple_of(width, VM_RANGE_CHECK_TABLE_WIDTH);
            constraint_bit_length_for_shifted_variable_assuming_8x8_table(
                cs,
                &num,
                shifts[shift_idx],
                new_width,
            )?;
            // constraint_bit_length_for_shifted_variable(cs, &num, shifts[shift_idx], new_width)?;
        }

        Ok(())
    }

    fn assert_orthigonality(markers: &[CtxMarker], flags: &[Boolean]) {
        assert_eq!(markers.len(), flags.len());
        assert!(has_unique_elements(markers.iter()));
        if flags
            .iter()
            .filter(|x| x.get_value().unwrap_or(false))
            .count()
            > 1
        {
            for (marker, flag) in markers.iter().zip(flags.iter()) {
                if flag.get_value().unwrap_or(false) {
                    println!("Marker {:?} has flag set", marker);
                }
            }

            panic!("Non-othogonal case");
        }
    }

    pub fn enforce_conditional_range_checks<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut elem_vec = std::mem::replace(&mut self.range_checks_queue, vec![]);

        while elem_vec.len() > 0 {
            let (current, remaining) = partition_dedup_by_key(elem_vec, |x| x.0);
            let len = current.len();
            let mut markers = Vec::<CtxMarker>::with_capacity(len);
            let mut applicability_flags = Vec::<Boolean>::with_capacity(len);
            let mut candidates = Vec::<Num<E>>::with_capacity(len);
            let mut widths = Vec::<usize>::with_capacity(len);

            for (marker, flag, relation) in current.iter().cloned() {
                markers.push(marker);
                applicability_flags.push(flag);
                candidates.push(relation.value);
                widths.push(relation.width);
            }

            Self::assert_orthigonality(&markers, &applicability_flags);

            // find the maximal possible width among all the candidates
            let max_width = widths.iter().fold(std::usize::MIN, |a, b| a.max(*b));
            let shifts = compute_shifts::<E::Fr>();
            let mut accumulator = Num::zero();

            let iter = candidates[..]
                .iter()
                .zip(applicability_flags[..].iter())
                .zip(widths[..].iter());
            for ((value, flag), width) in iter {
                let shift = shifts[max_width - width];
                if value.is_constant() && flag.is_constant() && accumulator.is_constant() {
                    let new_acc_val = if flag.get_value().unwrap() {
                        let mut tmp = value.get_constant_value();
                        tmp.mul_assign(&shift);
                        tmp.add_assign(&accumulator.get_constant_value());
                        tmp
                    } else {
                        accumulator.get_constant_value()
                    };
                    accumulator = Num::Constant(new_acc_val);
                    continue;
                }

                // new_acc = acc + shift * value * flag
                // shift * value * flag + acc - new_acc = 0
                let mut gate = MainGateTerm::new();
                let mut cnst_term = E::Fr::zero();

                match (value, flag) {
                    (Num::Constant(fr), Boolean::Constant(bit)) => {
                        if *bit {
                            let mut tmp = fr.clone();
                            tmp.mul_assign(&shift);
                            cnst_term.add_assign(&tmp);
                        }
                    }
                    (Num::Constant(fr), Boolean::Is(flag)) => {
                        let mut coef = fr.clone();
                        coef.mul_assign(&shift);
                        let term =
                            ArithmeticTerm::from_variable_and_coeff(flag.get_variable(), coef);
                        gate.add_assign(term);
                    }
                    (Num::Constant(fr), Boolean::Not(flag)) => {
                        let mut coef = fr.clone();
                        coef.mul_assign(&shift);
                        let term =
                            ArithmeticTerm::from_variable_and_coeff(flag.get_variable(), coef);
                        gate.sub_assign(term);
                        cnst_term.add_assign(&coef);
                    }
                    (Num::Variable(var), Boolean::Constant(bit)) => {
                        if *bit {
                            let term =
                                ArithmeticTerm::from_variable_and_coeff(var.get_variable(), shift);
                            gate.add_assign(term);
                        }
                    }
                    (Num::Variable(var), Boolean::Is(flag)) => {
                        let term = {
                            let tmp =
                                ArithmeticTerm::from_variable_and_coeff(var.get_variable(), shift);
                            tmp.mul_by_variable(flag.get_variable())
                        };
                        gate.add_assign(term);
                    }
                    (Num::Variable(var), Boolean::Not(flag)) => {
                        // coef * var * (1-flag) = coef * var - coef * var * flag
                        let first_term =
                            ArithmeticTerm::from_variable_and_coeff(var.get_variable(), shift);
                        gate.add_assign(first_term.clone());
                        let second_term = first_term.mul_by_variable(flag.get_variable());
                        gate.sub_assign(second_term);
                    }
                };

                match accumulator {
                    Num::Constant(fr) => cnst_term.add_assign(&fr),
                    Num::Variable(var) => {
                        gate.add_assign(ArithmeticTerm::from_variable(var.get_variable()))
                    }
                };
                gate.add_assign(ArithmeticTerm::constant(cnst_term));

                let new_acc_var = AllocatedNum::alloc(cs, || {
                    let mut tmp = value.get_value().grab()?;
                    tmp.mul_assign(&shift);
                    tmp.mul_assign(&flag.get_value_in_field::<E>().grab()?);
                    tmp.add_assign(&accumulator.get_value().grab()?);
                    Ok(tmp)
                })?;

                gate.sub_assign(ArithmeticTerm::from_variable(new_acc_var.get_variable()));
                cs.allocate_main_gate(gate)?;
                accumulator = Num::Variable(new_acc_var);
            }

            let shift_idx = max_width % VM_RANGE_CHECK_TABLE_WIDTH;
            let new_width = next_multiple_of(max_width, VM_RANGE_CHECK_TABLE_WIDTH);
            constraint_bit_length_for_shifted_variable_assuming_8x8_table(
                cs,
                &accumulator,
                shifts[shift_idx],
                new_width,
            )?;
            // constraint_bit_length_for_shifted_variable(cs, &accumulator, shifts[shift_idx], new_width)?;

            elem_vec = remaining;
        }

        Ok(())
    }

    pub fn allocate_boolean<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        witness: Option<bool>,
    ) -> Result<Boolean, SynthesisError> {
        // allocate as unchecked, but later on we will ensure correctness
        let allocated_num = AllocatedNum::alloc(cs, || {
            let bool = witness.grab()?;
            if bool {
                Ok(E::Fr::one())
            } else {
                Ok(E::Fr::zero())
            }
        })?;
        let bit = AllocatedBit::from_allocated_num_unchecked(allocated_num);
        let boolean = Boolean::Is(bit);
        self.boolean_constraints_queue.push(allocated_num);

        Ok(boolean)
    }

    pub fn enforce_boolean_allocations<CS>(&mut self, cs: &mut CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        const NUM_PER_GATE: usize = 3;
        let mut boolean_constraints_queue =
            std::mem::replace(&mut self.boolean_constraints_queue, vec![]);
        if boolean_constraints_queue.len() % NUM_PER_GATE != 0 {
            let to_add = NUM_PER_GATE - boolean_constraints_queue.len() % NUM_PER_GATE;
            for _ in 0..to_add {
                let allocated_num = AllocatedNum::alloc(cs, || Ok(E::Fr::zero()))?;
                boolean_constraints_queue.push(allocated_num);
            }
        }
        use crate::precompiles::utils::table_width_3_lookup;

        for chunk in boolean_constraints_queue.chunks_exact(NUM_PER_GATE) {
            // use 1bit X 1bit X 1bit table
            let lookup_over: Vec<_> = chunk.iter().map(|el| Num::Variable(*el)).collect();
            let _ = table_width_3_lookup(cs, VM_BOOLEAN_BATCH_ALLOCATION_TABLE_NAME, &lookup_over)?;
        }

        Ok(())
    }
}

impl<E: Engine> Drop for OptimizationContext<E> {
    fn drop(&mut self) {
        assert!(self.range_checks_queue.is_empty());
        assert!(self.unconditional_range_checks.is_empty());
        assert!(self.uint256_addsub_tuples.is_empty());
        assert!(self.uint256_divmul_tuples.is_empty());
        assert!(self.zero_checks_tuples.is_empty());
        assert!(self.boolean_constraints_queue.is_empty());
    }
}
