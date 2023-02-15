use super::zeroable_point::*;
use super::*;
use rescue_poseidon::{CircuitGenericSponge, GenericSponge, HashParams};
pub trait TranscriptGadget<E: Engine> {
    type Params: Clone + serde::Serialize + serde::de::DeserializeOwned;

    fn new(params: &Self::Params) -> Self;

    fn commit_scalar<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        data: Num<E>,
    ) -> Result<(), SynthesisError>;

    fn commit_point<'a, CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        point: &PointAffine<'a, E, E::G1Affine>,
    ) -> Result<(), SynthesisError>;

    fn get_challenge<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<Num<E>, SynthesisError>;
}

pub struct GenericTranscriptGadget<
    E: Engine,
    P: HashParams<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
> {
    state: CircuitGenericSponge<E, AWIDTH, SWIDTH>,
    params: P,
}

impl<E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    TranscriptGadget<E> for GenericTranscriptGadget<E, P, AWIDTH, SWIDTH>
{
    type Params = P;

    fn new(channel_params: &Self::Params) -> Self {
        Self {
            state: CircuitGenericSponge::new(),
            params: channel_params.clone(),
        }
    }

    fn commit_scalar<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        data: Num<E>,
    ) -> Result<(), SynthesisError> {
        self.state.absorb(cs, data, &self.params)?;

        Ok(())
    }

    fn commit_point<'a, CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        point: &PointAffine<'a, E, E::G1Affine>,
    ) -> Result<(), SynthesisError> {
        let num_limbs_in_field = point
            .non_zero_point
            .x
            .representation_params
            .num_limbs_for_in_field_representation;
        point.non_zero_point.x.clone().enforce_is_normalized(cs)?;
        point.non_zero_point.y.clone().enforce_is_normalized(cs)?;
        for coord_limbs in [
            &point.non_zero_point.x.binary_limbs,
            &point.non_zero_point.y.binary_limbs,
        ]
        .iter()
        {
            for limb in coord_limbs.iter().take(num_limbs_in_field) {
                let as_num = limb.collapse_into_num(cs)?;
                self.state.absorb(cs, as_num, &self.params)?;
            }
        }

        Ok(())
    }

    fn get_challenge<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<Num<E>, SynthesisError> {
        // self.state.pad_if_necessary()?;
        self.state.pad_if_necessary();
        let temp = self
            .state
            .squeeze_num(cs, &self.params)?
            .expect("squeezed value");

        Ok(temp)
    }
}

use crate::bellman::plonk::commitments::transcript::*;
use franklin_crypto::plonk::circuit::bigint::bigint::*;
use franklin_crypto::rescue::*;

#[derive(Clone)]
pub struct GenericTranscriptForRNSInFieldOnly<
    'a,
    E: Engine,
    P: HashParams<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
> {
    state: GenericSponge<E, AWIDTH, SWIDTH>,
    hash_params: &'a P,
    rns_parameters: &'a RnsParameters<E, <<E as Engine>::G1Affine as CurveAffine>::Base>,
}

impl<'a, E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    Prng<E::Fr> for GenericTranscriptForRNSInFieldOnly<'a, E, P, AWIDTH, SWIDTH>
{
    type Input = E::Fr;
    type InitializationParameters = (
        &'a P,
        &'a RnsParameters<E, <<E as Engine>::G1Affine as CurveAffine>::Base>,
    );

    #[track_caller]
    fn new() -> Self {
        unimplemented!("must initialize from parameters");
    }

    fn new_from_params(params: Self::InitializationParameters) -> Self {
        let (hash_params, rns_params) = params;
        let stateful = GenericSponge::new();

        Self {
            state: stateful,
            hash_params: &hash_params,
            rns_parameters: rns_params,
        }
    }

    fn commit_input(&mut self, input: &Self::Input) {
        self.state.absorb(*input, self.hash_params);
    }

    fn get_challenge(&mut self) -> E::Fr {
        self.state.pad_if_necessary();
        let value = self
            .state
            .squeeze(self.hash_params)
            .expect("squeezed value");

        value
    }
}

impl<'a, E: Engine, P: HashParams<E, AWIDTH, SWIDTH>, const AWIDTH: usize, const SWIDTH: usize>
    Transcript<E::Fr> for GenericTranscriptForRNSInFieldOnly<'a, E, P, AWIDTH, SWIDTH>
{
    fn commit_bytes(&mut self, _bytes: &[u8]) {
        unimplemented!();
    }

    fn commit_field_element(&mut self, element: &E::Fr) {
        self.state.absorb(*element, self.hash_params);
    }

    fn get_challenge_bytes(&mut self) -> Vec<u8> {
        unimplemented!();
    }

    fn commit_fe<FF: PrimeField>(&mut self, element: &FF) {
        let expected_field_char =
            <<<E as Engine>::G1Affine as CurveAffine>::Base as PrimeField>::char();
        let this_field_char = FF::char();
        assert_eq!(
            expected_field_char.as_ref(),
            this_field_char.as_ref(),
            "can only commit base curve field element"
        );

        // convert into RNS limbs

        let params = self.rns_parameters;
        let num_limbs_in_field = params.num_limbs_for_in_field_representation;

        let value = fe_to_biguint(element);

        let mut witness_limbs_proto = split_into_fixed_number_of_limbs(
            value,
            params.binary_limbs_params.limb_size_bits,
            params.num_binary_limbs,
        );

        let witness_limbs: Vec<_> = witness_limbs_proto.drain(0..num_limbs_in_field).collect();
        for l in witness_limbs_proto.into_iter() {
            let tmp: E::Fr = biguint_to_fe(l);
            assert!(tmp.is_zero());
        }

        let limb_values: Vec<E::Fr> = witness_limbs
            .into_iter()
            .map(|el| biguint_to_fe(el))
            .collect();

        for el in limb_values.into_iter() {
            self.state.absorb(el, self.hash_params);
        }
    }
}
