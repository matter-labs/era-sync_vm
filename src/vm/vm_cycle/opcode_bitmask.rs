use super::*;

use zkevm_opcode_defs::{
    ISAVersion, ImmMemHandlerFlags, OPCODE_INPUT_VARIANT_FLAGS, OPCODE_OUTPUT_VARIANT_FLAGS,
    OPCODE_TYPE_BITS, TOTAL_AUX_BITS,
};

// opcode defs only provide runtime-computeable variable, so we have to pin ISA version and assert

pub const SUPPORTED_ISA_VERSION: ISAVersion = ISAVersion(1);

const _: () = if SUPPORTED_ISA_VERSION.0 != zkevm_opcode_defs::DEFAULT_ISA_VERSION.0 {
    panic!()
} else {
    ()
};

pub(crate) const OPCODE_VARIANT_BITS: usize = 10;
pub(crate) const OPCODE_FLAGS_BITS: usize = 2;
pub(crate) const TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED: usize = 48;
pub(crate) const TOTAL_OPCODE_DESCRIPTION_AND_AUX_BITS: usize =
    TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED + TOTAL_AUX_BITS;

/// We hide all the source selection and updating in preprocessing,
/// so we only need imms and some variant properties
#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct UsedOpcode<E: Engine> {
    pub properties_bitmask: OpcodeBitmask<E>,
    pub imm0: UInt16<E>,
    pub imm1: UInt16<E>,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct OpcodeBitmask<E: Engine> {
    pub opcode_type_booleans: [Boolean; OPCODE_TYPE_BITS],
    pub opcode_variant_booleans: [Boolean; OPCODE_VARIANT_BITS],
    pub flag_booleans: [Boolean; OPCODE_FLAGS_BITS],
    pub input_variant_booleans: [Boolean; OPCODE_INPUT_VARIANT_FLAGS],
    pub output_variant_booleans: [Boolean; OPCODE_OUTPUT_VARIANT_FLAGS],
    _marker: std::marker::PhantomData<E>,
}

use zkevm_opcode_defs::Opcode;

impl<E: Engine> OpcodeBitmask<E> {
    pub fn boolean_for_opcode(&self, opcode: Opcode) -> Boolean {
        let opcode_idx = opcode.variant_idx();
        self.opcode_type_booleans[opcode_idx]
    }

    pub fn boolean_for_variant(&self, opcode: Opcode) -> Boolean {
        let variant_idx = opcode.materialize_subvariant_idx();
        self.opcode_variant_booleans[variant_idx]
    }

    pub fn boolean_for_src_mem_access(&self, access_type: ImmMemHandlerFlags) -> Boolean {
        let variant_idx = access_type.variant_index();
        self.input_variant_booleans[variant_idx]
    }

    pub fn boolean_for_dst_mem_access(&self, access_type: ImmMemHandlerFlags) -> Boolean {
        assert!(access_type.is_allowed_for_dst());
        let variant_idx = access_type.variant_index();
        self.output_variant_booleans[variant_idx]
    }

    pub fn from_full_mask(mask: [Boolean; TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED]) -> Self {
        // assert to not mismatch alignments
        assert_eq!(
            OPCODE_VARIANT_BITS,
            zkevm_opcode_defs::max_num_variants_for_version(SUPPORTED_ISA_VERSION)
        );
        assert_eq!(
            OPCODE_FLAGS_BITS,
            zkevm_opcode_defs::max_num_flags_for_version(SUPPORTED_ISA_VERSION)
        );
        assert_eq!(
            TOTAL_OPCODE_DESCRIPTION_BITS_FLATTENED,
            zkevm_opcode_defs::total_description_bits_rounded_for_version(SUPPORTED_ISA_VERSION)
        );

        let mut offset = 0;
        let opcode_type_booleans: [Boolean; OPCODE_TYPE_BITS] = mask
            [offset..(offset + OPCODE_TYPE_BITS)]
            .try_into()
            .unwrap();
        offset += OPCODE_TYPE_BITS;
        let opcode_variant_booleans: [Boolean; OPCODE_VARIANT_BITS] = mask
            [offset..(offset + OPCODE_VARIANT_BITS)]
            .try_into()
            .unwrap();
        offset += OPCODE_VARIANT_BITS;
        let flag_booleans: [Boolean; OPCODE_FLAGS_BITS] = mask
            [offset..(offset + OPCODE_FLAGS_BITS)]
            .try_into()
            .unwrap();
        offset += OPCODE_FLAGS_BITS;
        let input_variant_booleans: [Boolean; OPCODE_INPUT_VARIANT_FLAGS] = mask
            [offset..(offset + OPCODE_INPUT_VARIANT_FLAGS)]
            .try_into()
            .unwrap();
        offset += OPCODE_INPUT_VARIANT_FLAGS;
        let output_variant_booleans: [Boolean; OPCODE_OUTPUT_VARIANT_FLAGS] = mask
            [offset..(offset + OPCODE_OUTPUT_VARIANT_FLAGS)]
            .try_into()
            .unwrap();

        Self {
            opcode_type_booleans,
            opcode_variant_booleans,
            flag_booleans,
            input_variant_booleans,
            output_variant_booleans,
            _marker: std::marker::PhantomData,
        }
    }
}
