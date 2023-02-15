use super::*;
use cs_derive::*;
use rescue_poseidon::{circuit_generic_round_function, generic_round_function, HashParams};
use std::convert::{TryFrom, TryInto};
use std::iter;

#[derive(Derivative, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable)]
#[derivative(Clone, Debug)]
pub struct GenericSpongeState<E: Engine, const SWIDTH: usize> {
    pub state: [Num<E>; SWIDTH],
}

impl<E: Engine, const SWIDTH: usize> Copy for GenericSpongeState<E, SWIDTH> {}

impl<E: Engine, const SWIDTH: usize> GenericSpongeState<E, SWIDTH> {
    pub fn new() -> Self {
        Self {
            state: [Num::Constant(E::Fr::zero()); SWIDTH],
        }
    }

    pub fn empty() -> Self {
        Self {
            state: [Num::Constant(E::Fr::zero()); SWIDTH],
        }
    }

    pub fn zero() -> Self {
        Self {
            state: [Num::Constant(E::Fr::zero()); SWIDTH],
        }
    }

    pub fn get_witness(&self) -> [Option<E::Fr>; SWIDTH] {
        let mut res = [None; SWIDTH];
        for (in_elem, out_elem) in self.state.iter().zip(res.iter_mut()) {
            *out_elem = in_elem.get_value();
        }
        res
    }

    pub fn placeholder_witness() -> [Option<E::Fr>; SWIDTH] {
        [Some(E::Fr::zero()); SWIDTH]
    }

    pub fn alloc_from_witness<CS>(
        cs: &mut CS,
        wit: [Option<E::Fr>; SWIDTH],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut state = [Num::zero(); SWIDTH];
        for (in_elem, out_elem) in wit.iter().zip(state.iter_mut()) {
            let var = AllocatedNum::alloc(cs, || in_elem.grab())?;
            *out_elem = Num::Variable(var);
        }

        Ok(Self { state })
    }

    pub fn default() -> Self {
        Self {
            state: [Num::Constant(E::Fr::zero()); SWIDTH],
        }
    }

    pub fn from_raw(raw_state: [Num<E>; SWIDTH]) -> Self {
        Self { state: raw_state }
    }

    pub fn from_slice(raw_state: &[Num<E>]) -> Self {
        let wrapped_state = <[Num<E>; SWIDTH]>::try_from(raw_state);
        Self {
            state: wrapped_state.unwrap(),
        }
    }

    pub fn absorb<CS: ConstraintSystem<E>, const AWIDTH: usize>(
        &self,
        cs: &mut CS,
        elems_to_absorb: GenericSpongeAbsorbElems<E, AWIDTH>,
    ) -> Result<Self, SynthesisError> {
        let mut new_state = self.state.clone();
        for (s, v) in new_state.iter_mut().zip(elems_to_absorb.state[..].iter()) {
            *s = s.add(cs, v)?;
        }

        let res = Self { state: new_state };
        Ok(res)
    }

    pub fn allocate_round_function_witness<CS, P, const AWIDTH: usize>(
        &self,
        cs: &mut CS,
        params: &P,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        P: HashParams<E, AWIDTH, SWIDTH>,
    {
        let mut raw_state = Num::get_value_multiple(&self.state);
        raw_state
            .as_mut()
            .map(|state| generic_round_function(params, state));

        let mut all_constants = true;
        for el in self.state.iter() {
            all_constants = all_constants && el.is_constant();
        }

        let mut new_state = [Num::Constant(E::Fr::zero()); SWIDTH];
        for (idx, new) in new_state.iter_mut().enumerate() {
            *new = if all_constants {
                let wit_value = raw_state.as_ref().map(|el| el[idx]).unwrap();
                Num::Constant(wit_value)
            } else {
                let wit_value = raw_state.as_ref().map(|el| el[idx]);
                Num::Variable(AllocatedNum::alloc(cs, || Ok(wit_value.grab()?))?)
            }
        }

        let res = Self { state: new_state };
        Ok(res)
    }

    pub fn enforce_round_function<CS, P, const AWIDTH: usize>(
        cs: &mut CS,
        state_init: &Self,
        state_final: &Self,
        params: &P,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
        P: HashParams<E, AWIDTH, SWIDTH>,
    {
        let mut state_as_lcs: [LinearCombination<E>; SWIDTH] = unsafe { std::mem::zeroed() };
        for (s, lc_loc) in state_init.state.iter().zip(state_as_lcs.iter_mut()) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&s, E::Fr::one());
            *lc_loc = lc;
        }

        // run round function
        circuit_generic_round_function(cs, &mut state_as_lcs, params)?;

        let mut new_state = [Num::<E>::zero(); SWIDTH];
        for (s, lc) in new_state.iter_mut().zip(state_as_lcs.into_iter()) {
            *s = lc.into_num(cs)?;
        }

        for (candidate, claimed_value) in new_state.iter().zip(state_final.state.iter()) {
            candidate.enforce_equal(cs, claimed_value)?;
        }

        Ok(())
    }

    pub fn round_function<
        CS: ConstraintSystem<E>,
        P: HashParams<E, AWIDTH, SWIDTH>,
        const AWIDTH: usize,
    >(
        &self,
        cs: &mut CS,
        params: &P,
    ) -> Result<Self, SynthesisError> {
        let mut state_as_lcs: [LinearCombination<E>; SWIDTH] = unsafe { std::mem::zeroed() };
        for (s, lc_loc) in self.state.iter().zip(state_as_lcs.iter_mut()) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&s, E::Fr::one());
            *lc_loc = lc;
        }

        // run round function
        circuit_generic_round_function(cs, &mut state_as_lcs, params)?;

        let mut new_state = [Num::<E>::zero(); SWIDTH];
        for (s, lc) in new_state.iter_mut().zip(state_as_lcs.into_iter()) {
            *s = lc.into_num(cs)?;
        }

        Ok(Self { state: new_state })
    }
}

#[derive(Derivative, CSEqual, CSSelectable, CSOrdering, CSOrthogonalSelectable)]
#[derivative(Clone, Debug)]
pub struct GenericSpongeAbsorbElems<E: Engine, const AWIDTH: usize> {
    pub state: [Num<E>; AWIDTH],
}

impl<E: Engine, const AWIDTH: usize> Copy for GenericSpongeAbsorbElems<E, AWIDTH> {}

impl<E: Engine, const AWIDTH: usize> GenericSpongeAbsorbElems<E, AWIDTH> {
    pub fn empty() -> Self {
        Self {
            state: [Num::Constant(E::Fr::zero()); AWIDTH],
        }
    }

    pub fn from_slice(raw_state: &[Num<E>]) -> Self {
        let wrapped_state = <[Num<E>; AWIDTH]>::try_from(raw_state);
        Self {
            state: wrapped_state.unwrap(),
        }
    }
}
