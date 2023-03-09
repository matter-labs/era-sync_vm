use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, Ident};

use crate::new_utils::{get_type_params_from_generics, prepend_engine_param_if_not_exist};

fn derive_fixed_len_decodable_ext_impl(original_struct: &DeriveInput) -> TokenStream {
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
        impl#generics CircuitFixedLengthDecodableExt<E, #enconding_length_constant_ident> for #ident<#type_params> {
            fn allocate_and_prove_encoding<CS: ConstraintSystem<E>>(cs: &mut CS, values: &[Num<E>; #enconding_length_constant_ident], witness: Option<Self::Witness>) -> Result<Self, SynthesisError> {
                let new = Self::allocate(cs, witness)?;
                let encoding = <Self as CircuitFixedLengthEncodable<E, #enconding_length_constant_ident>>::encode(&new, cs)?;

                for (enc, val) in encoding.iter().zip(values.iter()) {
                    enc.enforce_equal(cs, val)?;
                }

                Ok(new)
            }
            fn allocate_and_prove_encoding_conditionally<CS: ConstraintSystem<E>>(cs: &mut CS, values: &[Num<E>; #enconding_length_constant_ident], should_execute: &Boolean, witness: Option<Self::Witness>) -> Result<Self, SynthesisError> {
                let new = Self::allocate(cs, witness)?;
                let encoding = <Self as CircuitFixedLengthEncodable<E, #enconding_length_constant_ident>>::encode(&new, cs)?;

                let mut tmp = vec![];

                for (enc, val) in encoding.iter().zip(values.iter()) {
                    let eq = Num::equals(cs, &enc,val)?;
                    tmp.push(eq);
                }

                let eq = smart_and(cs, &tmp)?;
                can_not_be_false_if_flagged(cs, &eq, should_execute)?;

                Ok(new)
            }
        }
    }
}

pub(crate) fn derive_decodable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let fixed_len_decodable_ext_impl = derive_fixed_len_decodable_ext_impl(&derived_input);

    let expanded = quote! {
        #fixed_len_decodable_ext_impl
    };

    TokenStream::from(expanded).into()
}
