use proc_macro2::{Ident, Span, TokenStream};

use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput};

use crate::new_utils::{get_type_params_from_generics, prepend_engine_param_if_not_exist};

pub(crate) fn derive_decodable(
    input: proc_macro::TokenStream,
    len_expression: TokenStream,
) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        mut generics,
        ..
    } = derived_input;

    let type_params = get_type_params_from_generics(&generics, &Comma(Span::call_site()), false);

    prepend_engine_param_if_not_exist(&mut generics);

    let inner_const_ident =
        syn::parse_str::<Ident>(&format!("__{}_circuit_decoding_len_inner", ident).to_lowercase())
            .unwrap();
    let private_mod_ident =
        syn::parse_str::<Ident>(&format!("__{}_private_consts_decodable", ident).to_lowercase())
            .unwrap();

    let expanded = quote! {
        mod #private_mod_ident {
            use super::*;

            type E = crate::bellman::pairing::bn256::Bn256;
            pub(crate) const #inner_const_ident: usize = #len_expression;
        }

        pub(crate) const #inner_const_ident: usize = self::#private_mod_ident::#inner_const_ident;

        impl#generics CircuitFixedLengthDecodableExt<E, {#inner_const_ident}> for #ident<#type_params> {
            fn allocate_from_witness<CS: ConstraintSystem<E>>(cs: &mut CS, witness: Option<Self::Witness>) -> Result<Self, SynthesisError> {
                <Self as CSAllocatable<E>>::alloc_from_witness(cs, witness)
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
