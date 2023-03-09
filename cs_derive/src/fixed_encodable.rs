use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, Expr};

use crate::{
    utils::{fetch_attr, get_type_params_from_generics, prepend_engine_param_if_not_exist},
    witness::derive_witness_struct,
};

pub(crate) const ENCODING_LENGTH_ATTR_NAME: &str = "EncodingLength";
pub(crate) const PACK_FN_NEEDS_CS_AS_ARG: &str = "PackWithCS";

fn derive_fixed_len_encodable_impl(original_struct: &DeriveInput) -> TokenStream {
    let DeriveInput {
        attrs,
        ident,
        mut generics,
        ..
    } = original_struct.clone();

    let fixed_len_str = fetch_attr(ENCODING_LENGTH_ATTR_NAME, &attrs).expect("fixed len attribute");
    let fixed_len_expr = syn::parse_str::<Expr>(&fixed_len_str).expect("length attr as Expr");
    let pack_fn_needs_cs_arg_str = fetch_attr(PACK_FN_NEEDS_CS_AS_ARG, &attrs).expect("a boolean");
    let pack_fn_needs_cs_arg =
        syn::parse_str::<Expr>(&pack_fn_needs_cs_arg_str).expect("has cs attr as Expr");
    let type_params = get_type_params_from_generics(&generics, &Comma(Span::call_site()), false);

    let pack_fn = if pack_fn_needs_cs_arg == syn::parse_str::<Expr>("true").unwrap() {
        quote! {
            self.pack(cs)?
        }
    } else {
        quote! {
            self.pack()
        }
    };
    prepend_engine_param_if_not_exist(&mut generics);

    quote! {
        impl#generics CircuitFixedLengthEncodable<E, #fixed_len_expr> for #ident<#type_params> {
            fn encode<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; #fixed_len_expr], SynthesisError> {
                Ok(#pack_fn)
            }
            // we don't this function by default
            // fn encoding_witness(&self) -> Option<[E::Fr; #fixed_len_expr]> {
            //     todo!()
            // }
        }
    }
}

fn derive_fixed_len_encodable_ext_impl(original_struct: &DeriveInput) -> TokenStream {
    let DeriveInput {
        attrs,
        ident,
        mut generics,
        ..
    } = original_struct.clone();
    let comma = Comma(Span::call_site());

    let fixed_len_str = fetch_attr(ENCODING_LENGTH_ATTR_NAME, &attrs).expect("fixed len attribute");
    let fixed_len_expr = syn::parse_str::<Expr>(&fixed_len_str).expect("length attr as Expr");

    let witness_struct = derive_witness_struct(original_struct.clone());
    let _witness_ident = witness_struct.ident;
    let witness_generics = witness_struct.generics;

    let _witness_type_params = get_type_params_from_generics(&witness_generics, &comma, false);
    let type_params = get_type_params_from_generics(&generics, &comma, false);

    prepend_engine_param_if_not_exist(&mut generics);

    quote! {
        impl#generics CircuitFixedLengthEncodableExt<E, #fixed_len_expr> for #ident<#type_params> {}
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
