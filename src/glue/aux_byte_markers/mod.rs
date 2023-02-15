use super::*;

pub const NUM_SUPPORTED_AUX_BYTES: usize = 4;

pub use zkevm_opcode_defs::system_params::{
    EVENT_AUX_BYTE, L1_MESSAGE_AUX_BYTE, PRECOMPILE_AUX_BYTE, STORAGE_AUX_BYTE,
};

pub fn aux_byte_for_storage<E: Engine>() -> Byte<E> {
    Byte::constant(STORAGE_AUX_BYTE)
}

pub fn aux_byte_for_event<E: Engine>() -> Byte<E> {
    Byte::constant(EVENT_AUX_BYTE)
}

pub fn aux_byte_for_l1_message<E: Engine>() -> Byte<E> {
    Byte::constant(L1_MESSAGE_AUX_BYTE)
}

pub fn aux_byte_for_precompile_call<E: Engine>() -> Byte<E> {
    Byte::constant(PRECOMPILE_AUX_BYTE)
}

pub fn aux_byte_set_and_props<E: Engine>() -> (
    [Byte<E>; NUM_SUPPORTED_AUX_BYTES],
    [bool; NUM_SUPPORTED_AUX_BYTES],
) {
    let markers = [
        aux_byte_for_storage(),
        aux_byte_for_l1_message(),
        aux_byte_for_event(),
        aux_byte_for_precompile_call(),
    ];

    let require_deduplication = [true, true, true, true];

    (markers, require_deduplication)
}
