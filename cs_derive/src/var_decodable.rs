use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::{quote};
use syn::{Visibility, Data, DeriveInput, Fields, Field, TypePath, TypeArray, GenericParam, Generics, Type, parse_macro_input, punctuated::Punctuated, token::{Comma}};

use crate::{new_utils::{has_engine_generic_param, prepend_engine_param_if_not_exist, get_empty_path_field_initialization_of_type, get_equivalent_type, get_type_params_from_generics, get_type_path_of_field, get_base_type_witness_fn_name_by_ident, get_witness_ident}, new_witness::derive_witness_struct};

pub(crate) fn derive_cs_var_decodable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput{
        attrs,
        ident,
        mut generics,
        data,
        ..
    } = derived_input;

    let type_params = get_type_params_from_generics(&generics, &Comma(Span::call_site()), false);

    prepend_engine_param_if_not_exist(&mut generics);

    let expanded = quote!{
        impl#generics CircuitFixedLengthDecodableExt<E, {#inner_const_ident}> for #ident<#type_params> {
            fn allocate_from_witness<CS: ConstraintSystem<E>>(cs: &mut CS, witness: Option<Self::Witness>) -> Result<Self, SynthesisError> {
                <Self as CSAllocatable<E>>::alloc_from_witness(cs, witness)
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}