use super::*;

use zkevm_opcode_defs::{
    CONDITIONAL_BITS_SHIFT, OPCODES_TABLE_WIDTH, VARIANT_AND_CONDITION_ENCODING_BITS,
};

pub const VARIANT_AND_CONDITION_ENCODING_MASK: u64 =
    crate::utils::bit_width_to_bitmask(VARIANT_AND_CONDITION_ENCODING_BITS);
pub const VARIANT_ENCODING_MASK: u64 = crate::utils::bit_width_to_bitmask(OPCODES_TABLE_WIDTH);
pub const OPCODE_PROPS_BITMASK_FOR_BITSPREAD_ENCODING: u64 =
    crate::utils::bit_width_to_bitmask(TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED);

use crate::precompiles::utils::table_width_3_lookup;
use crate::vm::ports::ArithmeticFlagsPort;

use zkevm_opcode_defs::{
    OPCODE_INPUT_VARIANT_FLAGS, OPCODE_OUTPUT_VARIANT_FLAGS, OPCODE_TYPE_BITS, TOTAL_AUX_BITS,
};

use crate::vm::vm_cycle::opcode_bitmask::{
    OPCODE_FLAGS_BITS, OPCODE_VARIANT_BITS, TOTAL_OPCODE_DESCRIPTION_AND_AUX_BITS,
    TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED,
};

const CONDITION_ENCODING_BITS: usize = 3;

const UNUSED_GAP: usize =
    VARIANT_AND_CONDITION_ENCODING_BITS - OPCODES_TABLE_WIDTH - CONDITION_ENCODING_BITS;

pub const NUM_BITS_BEFORE_AUX_INFORMATION: usize = OPCODE_TYPE_BITS
    + OPCODE_VARIANT_BITS
    + OPCODE_FLAGS_BITS
    + OPCODE_INPUT_VARIANT_FLAGS
    + OPCODE_OUTPUT_VARIANT_FLAGS;

pub fn encode_flags<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    flags: &ArithmeticFlagsPort<E>,
) -> Result<Num<E>, SynthesisError> {
    let one = E::Fr::one();
    let mut two = one;
    two.double();
    let mut four = two;
    four.double();

    let mut lc = LinearCombination::zero();
    lc.add_assign_boolean_with_coeff(&flags.overflow_or_less_than, one);
    lc.add_assign_boolean_with_coeff(&flags.equal, two);
    lc.add_assign_boolean_with_coeff(&flags.greater_than, four);

    lc.into_num(cs)
}

pub struct OpcodeInitialDecoding<E: Engine> {
    pub condition: Boolean,
    pub opcode_boolean_spread_data: Num<E>, // this has both flags that describe the opcode itself, and aux flags for EH
    pub src_regs_encoding: UInt8<E>,
    pub dst_regs_encoding: UInt8<E>,
    pub imm0: UInt16<E>,
    pub imm1: UInt16<E>,
    pub ergs_cost: UInt32<E>,
}

pub fn split_out_aux_bits<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    opcode_boolean_spread_data: Num<E>,
    optimizer: &mut OptimizationContext<E>,
) -> Result<(Num<E>, [Boolean; TOTAL_AUX_BITS]), SynthesisError> {
    assert!(TOTAL_OPCODE_DESCRIPTION_AND_AUX_BITS <= 64);
    let (opcode_props, aux_props) = match opcode_boolean_spread_data.get_value() {
        Some(witness) => {
            let witness = fe_to_u64(witness);
            let props = witness & OPCODE_PROPS_BITMASK_FOR_BITSPREAD_ENCODING; // bits without AUX flag
                                                                               // println!("Opcode properties without aux flags = 0b{:048b}", props);
            assert!(OPCODE_PROPS_BITMASK_FOR_BITSPREAD_ENCODING < u64::MAX);
            let aux_bits_as_u64 = witness >> TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED;
            // println!("Aux bits = 0b{:03b}", aux_bits_as_u64);
            let mut aux_bits_as_u64 = aux_bits_as_u64 as u64;
            let mut aux_bits = Vec::with_capacity(TOTAL_AUX_BITS);
            for _ in 0..TOTAL_AUX_BITS {
                let bit = (aux_bits_as_u64 & 1u64) == 1;
                aux_bits.push(bit);
                aux_bits_as_u64 >>= 1;
            }
            assert!(aux_bits_as_u64 == 0);

            (Some(u64_to_fe::<E::Fr>(props)), Some(aux_bits))
        }
        _ => (None, None),
    };
    let opcode_props = Num::alloc(cs, opcode_props)?;
    // it may be unnecessary as be bitspread later on
    let _ = constraint_bit_length_assuming_8x8_table(
        cs,
        &opcode_props,
        TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED,
    )?;
    let shifts = compute_shifts::<E::Fr>();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&opcode_props, shifts[0]);
    let mut aux_bits = [Boolean::constant(false); TOTAL_AUX_BITS];
    let mut shift = TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED;
    for i in 0..TOTAL_AUX_BITS {
        let wit = aux_props.as_ref().map(|el| el[i]);
        let flag = optimizer.allocate_boolean(cs, wit)?;
        aux_bits[i] = flag;
        lc.add_assign_boolean_with_coeff(&flag, shifts[shift]);
        shift += 1;
    }
    assert_eq!(shift, TOTAL_OPCODE_DESCRIPTION_AND_AUX_BITS);
    lc.add_assign_number_with_coeff(&opcode_boolean_spread_data, minus_one);
    lc.enforce_zero(cs)?;

    Ok((opcode_props, aux_bits))
}

/// Decodes only necessary parts of the opcode to resolve condition
/// for masking into NOP if opcode does nothing.
/// We also output imm0/imm1 parts that will NOT be ever masked,
/// and register index encoding parts too that would be masked into 0.
/// Please remember that we mask only bitspread part after condition is resolved, and we do not need
/// to recompute the cost(!)
pub fn partially_decode_from_uint64_and_resolve_condition<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    opcode_word: UInt64<E>,
    encoded_flags: Num<E>,
    optimizer: &mut OptimizationContext<E>,
) -> Result<OpcodeInitialDecoding<E>, SynthesisError> {
    let (variant_wit, unused_bits_wit, condition_wit, rest_wit) = match opcode_word.get_value() {
        Some(wit) => {
            let variant_and_condition = wit & VARIANT_AND_CONDITION_ENCODING_MASK;
            let variant = variant_and_condition & VARIANT_ENCODING_MASK;
            let unused_bits =
                (variant_and_condition >> OPCODES_TABLE_WIDTH) & bit_width_to_bitmask(UNUSED_GAP);
            let unused_bit_0 = unused_bits & 1 > 0;
            let unused_bit_1 = (unused_bits >> 1) & 1 > 0;
            let condition = variant_and_condition >> CONDITIONAL_BITS_SHIFT;

            // dbg!(&zkevm_opcode_defs::OPCODES_TABLE[variant as usize]);
            // dbg!(&condition);

            let rest = wit >> VARIANT_AND_CONDITION_ENCODING_BITS;
            (
                Some(variant),
                Some([unused_bit_0, unused_bit_1]),
                Some(condition),
                Some(rest),
            )
        }
        _ => (None, None, None, None),
    };
    let rest = Num::alloc(cs, rest_wit.map(|el| u64_to_fe(el)))?;
    let variant = Num::alloc(cs, variant_wit.map(|el| u64_to_fe(el)))?;
    let condition = Num::alloc(cs, condition_wit.map(|el| u64_to_fe(el)))?;

    // constraint unused bits to be bits, but we do not care (yet) about it's particular value
    let unused_bit_0 = optimizer.allocate_boolean(cs, unused_bits_wit.map(|el| el[0]))?;
    let unused_bit_1 = optimizer.allocate_boolean(cs, unused_bits_wit.map(|el| el[1]))?;

    // bit check the length of rest
    let chunks = constraint_bit_length_assuming_8x8_table(
        cs,
        &rest,
        64 - VARIANT_AND_CONDITION_ENCODING_BITS,
    )?;
    assert_eq!(chunks.len(), 6);
    let src_regs_encoding = UInt8::from_num_unchecked(chunks[0]);
    let dst_regs_encoding = UInt8::from_num_unchecked(chunks[1]);

    let shifts = compute_shifts::<E::Fr>();
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&chunks[2], shifts[0]);
    lc.add_assign_number_with_coeff(&chunks[3], shifts[8]);
    let imm0 = UInt16::from_num_unchecked(lc.into_num(cs)?);

    let shifts = compute_shifts::<E::Fr>();
    let mut lc = LinearCombination::zero();
    lc.add_assign_number_with_coeff(&chunks[4], shifts[0]);
    lc.add_assign_number_with_coeff(&chunks[5], shifts[8]);
    let imm1 = UInt16::from_num_unchecked(lc.into_num(cs)?);

    // bit check variant and spread it
    let lookup = table_width_3_lookup(cs, VM_OPCODE_DECODING_AND_PRICING_TABLE_NAME, &[variant])?;
    let opcode_cost = UInt32::from_num_unchecked(lookup[0]);
    let opcode_properties = lookup[1];

    // condition is checked to be 3 bits through resolution here
    let lookup = table_width_3_lookup(
        cs,
        VM_CONDITIONAL_RESOLUTION_TABLE_NAME,
        &[condition, encoded_flags],
    )?;
    let resolution_bit = lookup[0];
    let resolution_bit = AllocatedBit::from_allocated_num_unchecked(resolution_bit.get_variable());
    let resolution = Boolean::from(resolution_bit);

    // enforce that we have chunked properly
    let mut lc = LinearCombination::zero();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    lc.add_assign_number_with_coeff(&variant, shifts[0]);
    let mut shift = OPCODES_TABLE_WIDTH;
    lc.add_assign_boolean_with_coeff(&unused_bit_0, shifts[shift]);
    shift += 1;
    lc.add_assign_boolean_with_coeff(&unused_bit_1, shifts[shift]);
    shift += 1;
    assert_eq!(shift, CONDITIONAL_BITS_SHIFT);
    lc.add_assign_number_with_coeff(&condition, shifts[CONDITIONAL_BITS_SHIFT]);
    lc.add_assign_number_with_coeff(&rest, shifts[VARIANT_AND_CONDITION_ENCODING_BITS]);
    lc.add_assign_number_with_coeff(&opcode_word.inner, minus_one);
    lc.enforce_zero(cs)?;

    let props = OpcodeInitialDecoding {
        condition: resolution,
        opcode_boolean_spread_data: opcode_properties,
        src_regs_encoding,
        dst_regs_encoding,
        imm0,
        imm1,
        ergs_cost: opcode_cost,
    };

    Ok(props)
}
