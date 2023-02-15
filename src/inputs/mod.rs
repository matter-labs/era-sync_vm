use super::*;
use crate::bellman::SynthesisError;
use crate::franklin_crypto::plonk::circuit::allocated_num::Num;
use crate::franklin_crypto::plonk::circuit::boolean::Boolean;
use crate::glue::optimizable_queue::commit_encodable_item;
use crate::glue::traits::*;
use crate::pairing::Engine;
use crate::vm::structural_eq::*;
use cs_derive::*;

#[derive(Derivative, CSWitnessable, CSAllocatable, CSVariableLengthEncodable)]
#[derivative(Clone, Debug)]
pub struct ClosedFormInput<
    E: Engine,
    T: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
    IN: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
    OUT: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
> where
    <T as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned + Eq,
    <IN as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned + Eq,
    <OUT as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned + Eq,
{
    pub start_flag: Boolean,
    pub completion_flag: Boolean,
    pub observable_input: IN,
    pub observable_output: OUT,
    pub hidden_fsm_input: T,
    pub hidden_fsm_output: T,
    pub _marker_e: std::marker::PhantomData<E>,
}

impl<
        E: Engine,
        T: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
        IN: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
        OUT: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
    > ClosedFormInput<E, T, IN, OUT>
where
    <T as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned + Eq,
    <IN as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned + Eq,
    <OUT as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned + Eq,
{
    pub fn alloc_ignoring_outputs<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        witness: Option<ClosedFormInputWitness<E, T, IN, OUT>>,
    ) -> Result<Self, SynthesisError>
    where
        T: CircuitEmpty<E>,
        OUT: CircuitEmpty<E>,
    {
        let (start_flag, observable_input, hidden_fsm_input) = match witness {
            Some(w) => {
                let ClosedFormInputWitness {
                    start_flag,
                    observable_input,
                    hidden_fsm_input,
                    ..
                } = w;

                (
                    Some(start_flag),
                    Some(observable_input),
                    Some(hidden_fsm_input),
                )
            }
            None => (None, None, None),
        };

        let start_flag = Boolean::alloc(cs, start_flag)?;
        let observable_input = IN::alloc_from_witness(cs, observable_input)?;
        let hidden_fsm_input = T::alloc_from_witness(cs, hidden_fsm_input)?;

        let new = Self {
            start_flag,
            completion_flag: Boolean::constant(false),
            observable_input,
            observable_output: OUT::empty(),
            hidden_fsm_input,
            hidden_fsm_output: T::empty(),
            _marker_e: std::marker::PhantomData,
        };

        Ok(new)
    }
}

#[derive(Derivative, CSWitnessable, CSAllocatable, CSPackable, CSEncodable, CSDecodable)]
#[derivative(Clone, Debug)]
pub struct ClosedFormInputCompactForm<E: Engine> {
    pub start_flag: Boolean,
    pub completion_flag: Boolean,
    pub observable_input_committment: Num<E>,
    pub observable_output_committment: Num<E>,
    pub hidden_fsm_input_committment: Num<E>,
    pub hidden_fsm_output_committment: Num<E>,
}

use crate::circuit_structures::traits::CircuitArithmeticRoundFunction;

impl<E: Engine> ClosedFormInputCompactForm<E> {
    pub fn from_full_form<
        CS: ConstraintSystem<E>,
        T: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
        IN: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
        OUT: std::fmt::Debug + CSAllocatable<E> + CircuitVariableLengthEncodableExt<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        cs: &mut CS,
        full_form: &ClosedFormInput<E, T, IN, OUT>,
        round_function: &R,
    ) -> Result<Self, SynthesisError>
    where
        <T as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned,
        <IN as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned,
        <OUT as CSWitnessable<E>>::Witness: serde::Serialize + serde::de::DeserializeOwned,
    {
        use crate::glue::optimizable_queue::commit_variable_length_encodable_item;

        let observable_input_committment =
            commit_variable_length_encodable_item(cs, &full_form.observable_input, round_function)?;
        let observable_output_committment = commit_variable_length_encodable_item(
            cs,
            &full_form.observable_output,
            round_function,
        )?;

        let hidden_fsm_input_committment =
            commit_variable_length_encodable_item(cs, &full_form.hidden_fsm_input, round_function)?;
        let hidden_fsm_output_committment = commit_variable_length_encodable_item(
            cs,
            &full_form.hidden_fsm_output,
            round_function,
        )?;

        // mask input. Observable part is NEVER masked
        // let observable_input_committment = Num::conditionally_select(
        //     cs,
        //     &full_form.start_flag,
        //     &observable_input_committment,
        //     &Num::zero()
        // )?;

        let hidden_fsm_input_committment = Num::conditionally_select(
            cs,
            &full_form.start_flag,
            &Num::zero(),
            &hidden_fsm_input_committment,
        )?;

        // mask output. Observable output is zero is not the last indeed
        let observable_output_committment = Num::conditionally_select(
            cs,
            &full_form.completion_flag,
            &observable_output_committment,
            &Num::zero(),
        )?;

        // and vice versa for FSM
        let hidden_fsm_output_committment = Num::conditionally_select(
            cs,
            &full_form.completion_flag,
            &Num::zero(),
            &hidden_fsm_output_committment,
        )?;

        let new = Self {
            start_flag: full_form.start_flag,
            completion_flag: full_form.completion_flag,
            observable_input_committment,
            observable_output_committment,
            hidden_fsm_input_committment,
            hidden_fsm_output_committment,
        };

        Ok(new)
    }
}
