use super::*;

use cs_derive::*;

#[derive(
    Derivative,
    CSWitnessable,
    CSAllocatable,
    CSEqual,
    CSSelectable,
    FixedLengthEncodableExt,
    FixedLengthDecodableExt,
)]
#[EncodingLength = "2"]
#[PackWithCS = "true"]
#[derivative(Clone, Debug)]
pub struct CodeKnowledgeRequestRecord<E: Engine> {
    pub target_is_zkporter: Boolean,
    pub code_root_hash: Num<E>,
}

impl<E: Engine> CodeKnowledgeRequestRecord<E> {
    pub fn pack<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<[Num<E>; 2], SynthesisError> {
        let mut lc = LinearCombination::zero();
        lc.add_assign_boolean_with_coeff(&self.target_is_zkporter, E::Fr::one());
        let el = lc.into_num(cs)?;

        Ok([el, self.code_root_hash])
    }
}
