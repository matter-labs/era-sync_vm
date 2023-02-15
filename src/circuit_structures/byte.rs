use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;

use super::traits::*;
use super::*;
use crate::derivative::*;
use franklin_crypto::plonk::circuit::bigint::{split_into_slices, split_some_into_slices};
pub use franklin_crypto::plonk::circuit::byte::*;
// use super::account_state::*;
// use super::stack::*;
use super::utils::*;
use super::WidthMarker;

impl<E: Engine, W: WidthMarker> IntoBytes<E> for SmallFixedWidthInteger<E, W> {
    fn into_le_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        assert!(W::WIDTH % 8 == 0);
        let num_bytes = W::WIDTH / 8;

        let result = match self.value {
            Num::Variable(ref var) => {
                let mut minus_one = E::Fr::one();
                minus_one.negate();
                let factor = E::Fr::from_str("256").unwrap();
                let mut coeff = E::Fr::one();
                let mut result = Vec::with_capacity(num_bytes);
                let mut lc = LinearCombination::zero();
                lc.add_assign_number_with_coeff(&self.value, minus_one);
                let witness = split_some_into_slices(var.get_value(), 8, num_bytes);
                for w in witness.into_iter() {
                    let allocated = AllocatedNum::alloc(cs, || Ok(*w.get()?))?;
                    let num = Num::Variable(allocated);
                    let byte = Byte::from_num(cs, num.clone())?;
                    result.push(byte);

                    lc.add_assign_number_with_coeff(&num, coeff);
                    coeff.mul_assign(&factor);
                }

                lc.enforce_zero(cs)?;

                result
            }
            Num::Constant(constant) => {
                let mut result = Vec::with_capacity(num_bytes);
                let witness = split_into_slices(&constant, 8, num_bytes);
                for w in witness.into_iter() {
                    let num = Num::Constant(w);
                    let byte = Byte::from_num(cs, num)?;
                    result.push(byte);
                }

                result
            }
        };

        Ok(result)
    }

    fn into_be_bytes<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<Vec<Byte<E>>, SynthesisError> {
        let mut tmp = self.into_le_bytes(cs)?;
        tmp.reverse();

        Ok(tmp)
    }
}
