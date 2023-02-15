use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct AggregationWitness<E: Engine, MG: MainGate<E>> {
    #[derivative(Debug = "ignore")]
    pub vk: VerificationKey<E, MainGateParametrizedCircuitWithNonlinearityAndLookups<E, MG>>,
    #[derivative(Debug = "ignore")]
    pub proof: Proof<E, MainGateParametrizedCircuitWithNonlinearityAndLookups<E, MG>>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct AggregationParameters<
    E: Engine,
    T: TranscriptGadget<E>,
    P: HashParams<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
> {
    pub base_placeholder_point: E::G1Affine,
    pub hash_params: P,

    #[derivative(Debug = "ignore")]
    #[serde(bound(serialize = "T::Params: serde::Serialize"))]
    #[serde(bound(deserialize = "T::Params: serde::de::DeserializeOwned"))]
    pub transcript_params: T::Params,
}
