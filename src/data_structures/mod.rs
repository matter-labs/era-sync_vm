use crate::bellman::SynthesisError;
use crate::derivative::*;
use crate::ff::*;
use crate::pairing::*;

pub mod alg_binary_tree;
pub mod markers;
pub mod state;
pub mod storage;

use self::markers::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SmallFixedWidthInteger<E: Engine, W: WidthMarker> {
    value: E::Fr,
    #[derivative(PartialEq = "ignore")]
    #[derivative(Debug = "ignore")]
    _marker: std::marker::PhantomData<W>,
}

impl<E: Engine, W: WidthMarker> SmallFixedWidthInteger<E, W> {
    pub fn new(value: E::Fr) -> Result<Self, SynthesisError> {
        let width = value.into_repr().num_bits() as usize;
        if width > W::WIDTH {
            return Err(SynthesisError::Unsatisfiable);
        }

        let new = Self {
            value: value,
            _marker: std::marker::PhantomData,
        };

        Ok(new)
    }

    pub fn extend<WW: WidthMarker>(&self) -> Result<SmallFixedWidthInteger<E, WW>, SynthesisError> {
        if WW::WIDTH >= W::WIDTH {
            Ok(SmallFixedWidthInteger::<E, WW> {
                value: self.value,
                _marker: std::marker::PhantomData,
            })
        } else {
            Err(SynthesisError::Unsatisfiable)
        }
    }

    pub fn into_value(&self) -> E::Fr {
        self.value
    }

    pub fn add_assign(&mut self, to_add: &Self) {
        self.value.add_assign(&to_add.value);
    }

    pub fn add_assign_fe(&mut self, to_add: &E::Fr) {
        self.value.add_assign(&to_add);
    }
}
