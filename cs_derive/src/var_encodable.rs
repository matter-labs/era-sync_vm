use proc_macro2::Span;

use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput};

use crate::new_utils::{get_type_params_from_generics, prepend_engine_param_if_not_exist};

pub(crate) fn derive_var_encodable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        mut generics,
        ..
    } = derived_input;

    let type_params = get_type_params_from_generics(&generics, &Comma(Span::call_site()), false);
    let where_clause = if let Some(clause) = generics.where_clause.as_ref() {
        quote! {
            #clause
        }
    } else {
        quote! {}
    };

    prepend_engine_param_if_not_exist(&mut generics);

    // we need expression to return length

    let expanded = quote! {
        impl#generics CircuitVariableLengthEncodable<E> for #ident<#type_params> #where_clause {
            fn encoding_length() -> usize {
                Self::variable_length_packing_length()
            }

            fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
                Self::variable_length_pack(self, cs)
            }
            // we don't need this function by default
            // fn encoding_witness(&self) -> Option<[E::Fr; #enconding_length_constant_ident]> {
            //     todo!()
            // }
        }

        impl#generics CircuitVariableLengthEncodableExt<E> for #ident<#type_params> #where_clause  {}
    };

    proc_macro::TokenStream::from(expanded)
}
