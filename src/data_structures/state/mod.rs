use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;

use super::*;
use crate::traits::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AccountState<E: Engine> {
    pub nonce: SmallFixedWidthInteger<E, U32>,
    pub balances_tree_root: E::Fr,
    pub ethereum_address: SmallFixedWidthInteger<E, U160>,
    pub sync_pubkey_hash: E::Fr,
    pub self_state: E::Fr,
    pub contract_code_root: E::Fr,
}

impl<E: Engine> AccountState<E> {
    pub fn empty() -> Self {
        Self {
            nonce: SmallFixedWidthInteger::<E, U32>::new(E::Fr::zero()).unwrap(),
            balances_tree_root: E::Fr::zero(),
            ethereum_address: SmallFixedWidthInteger::<E, U160>::new(E::Fr::zero()).unwrap(),
            sync_pubkey_hash: E::Fr::zero(),
            self_state: E::Fr::zero(),
            contract_code_root: E::Fr::zero(),
        }
    }
}

impl<E: Engine> ArithmeticEncodable<E> for AccountState<E> {
    fn encoding_length() -> usize {
        6
    }

    fn encode(&self) -> Result<Vec<E::Fr>, SynthesisError> {
        let mut values = vec![];
        values.push(self.nonce.into_value());
        values.push(self.balances_tree_root);
        values.push(self.ethereum_address.into_value());
        values.push(self.sync_pubkey_hash);
        values.push(self.self_state);
        values.push(self.contract_code_root);

        Ok(values)
    }
}

impl<E: Engine> ArithmeticCommitable<E> for AccountState<E> {}
