use super::*;
use std::collections::HashMap;
use std::marker::PhantomData;
use crate::vm::opcodes::*;


#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct OpcodeMap<E: Engine> {
    pub opcode: UInt8<E>,
    pub inner_map: HashMap<&'static str, Boolean>,
}

impl<E: Engine> OpcodeMap<E>{
    pub fn empty(opcode_byte: &UInt8<E>) -> Self {
        OpcodeMap {
            opcode: opcode_byte.clone(),
            inner_map: HashMap::new(),
        }
    }

    pub fn check_and_get<CS, O>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError>
    where CS: ConstraintSystem<E>, O: OpCode<E>
    {
        let key = O::short_description();
        let res = match self.inner_map.get(&key) {
            Some(x) => x.clone(),
            None => {
                let is_executed = Self::is_executed_opcode::<_, O>(cs, &self.opcode)?;
                self.inner_map.insert(key, is_executed);
                is_executed
            }
        };
        
        Ok(res)
    }

    fn is_executed_opcode<CS: ConstraintSystem<E>, O: OpCode<E>>(
        cs: &mut CS, this_cycle_opcode_byte: &UInt8<E>,
    ) -> Result<Boolean, SynthesisError> {
        Num::equals(cs, &this_cycle_opcode_byte.inner, &Num::Constant(u64_to_fe(O::opcode() as u64)))
    }

    pub fn create_full_opcode_map<CS>(cs: &mut CS, this_cycle_byte: UInt8<E>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let mut execute_opcode_map = HashMap::new();
        macro_rules! check_if_executed {
            ($opcode:ty) => { 
                let is_executed = Self::is_executed_opcode::<_, $opcode>(cs, &this_cycle_byte)?;
                let key = <$opcode>::short_description();
                assert!(execute_opcode_map.get(&key).is_none());
                execute_opcode_map.insert(key, is_executed);
            };
        }

        check_if_executed!(NoopOpcode<E>);
        check_if_executed!(AddOpcode::<E>); 
        check_if_executed!(SubOpcode::<E>); 
        check_if_executed!(MulOpcode::<E>);
        check_if_executed!(DivOpcode::<E>);
        check_if_executed!(JumpOpcode::<E>);
        check_if_executed!(BitwiseLogicalOpcode::<E>);
        check_if_executed!(ShiftOpcode::<E>);
        check_if_executed!(GetFromContextOpcode::<E>);
        check_if_executed!(CMoveOpcode::<E>);
        check_if_executed!(NearCallOpcode::<E>);
        check_if_executed!(FarCallOpcode::<E>);
        check_if_executed!(RetOpcode::<E>);
        check_if_executed!(LogOpcode::<E>);

        Ok(OpcodeMap {
            opcode: this_cycle_byte.clone(),
            inner_map: execute_opcode_map,
        })
    }
}

    