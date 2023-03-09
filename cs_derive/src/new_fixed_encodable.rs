use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, Ident};

use crate::{
    new_utils::{get_type_params_from_generics, prepend_engine_param_if_not_exist},
    new_witness::derive_witness_struct,
};

fn derive_fixed_len_encodable_impl(original_struct: &DeriveInput) -> TokenStream {
    let DeriveInput {
        ident,
        mut generics,
        ..
    } = original_struct.clone();

    let type_params = get_type_params_from_generics(&generics, &Comma(Span::call_site()), false);

    prepend_engine_param_if_not_exist(&mut generics);

    let enconding_length_constant_ident =
        syn::parse_str::<Ident>(&format!("{}CircuitEncodingLength", ident)).unwrap();

    quote! {
        impl#generics CircuitFixedLengthEncodable<E, #enconding_length_constant_ident> for #ident<#type_params> {
            fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; #enconding_length_constant_ident], SynthesisError> {
                Ok(self.pack(cs)?)
            }
            // we don't need this function by default
            // fn encoding_witness(&self) -> Option<[E::Fr; #enconding_length_constant_ident]> {
            //     todo!()
            // }
        }
    }
}

fn derive_fixed_len_encodable_ext_impl(original_struct: &DeriveInput) -> TokenStream {
    let DeriveInput {
        ident,
        mut generics,
        ..
    } = original_struct.clone();
    let comma = Comma(Span::call_site());

    let witness_struct = derive_witness_struct(original_struct.clone());
    let witness_ident = witness_struct.ident;
    let witness_generics = witness_struct.generics;

    let witness_type_params = get_type_params_from_generics(&witness_generics, &comma, false);
    let type_params = get_type_params_from_generics(&generics, &comma, false);

    prepend_engine_param_if_not_exist(&mut generics);

    let enconding_length_constant_ident =
        syn::parse_str::<Ident>(&format!("{}CircuitEncodingLength", ident)).unwrap();

    quote! {
        impl#generics CircuitFixedLengthEncodableExt<E, #enconding_length_constant_ident> for #ident<#type_params> {
            type Witness = #witness_ident<#witness_type_params>;

            fn create_witness(&self) -> Option<Self::Witness> {
                self.get_witness()
            }

            fn placeholder_witness() -> Self::Witness {
                #witness_ident::<#witness_type_params>::empty()
            }
        }
    }
}

pub(crate) fn derive_encodable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let fixed_len_encodable_impl = derive_fixed_len_encodable_impl(&derived_input);
    let fixed_len_encodable_ext_impl = derive_fixed_len_encodable_ext_impl(&derived_input);

    let expanded = quote! {
        #fixed_len_encodable_impl
        #fixed_len_encodable_ext_impl
    };

    TokenStream::from(expanded).into()
}
