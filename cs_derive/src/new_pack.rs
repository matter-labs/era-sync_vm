use proc_macro2::{Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Comma, DeriveInput, GenericParam, Generics,
    Ident, Type,
};

use crate::new_utils::{
    get_encoding_length_expression_of_type, get_packing_function_of_type,
    get_type_params_from_generics, has_engine_generic_param,
};

pub(crate) fn derive_pack(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        generics,
        data,
        vis,
        ..
    } = derived_input.clone();

    let type_params = get_type_params_from_generics(&generics, &Comma(Span::call_site()), false);

    let enconding_length_constant_ident =
        syn::parse_str::<Ident>(&format!("{}CircuitEncodingLength", ident)).unwrap();
    let mut encoding_length_expression = TokenStream::new();
    let mut packing = TokenStream::new();
    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("a field ident");

                    let (field_enconding_length, field_packing) = match field.ty {
                        Type::Array(ref array_ty) => {
                            match *array_ty.elem {
                                Type::Path(ref _p) => {}
                                _ => abort_call_site!("only array of elements is allowed here"),
                            };

                            let array_enconding_length =
                                get_encoding_length_expression_of_type(&field.ty);
                            let (push_fn, pack_fn) = get_packing_function_of_type(&field.ty);
                            let field_packing = quote! {
                                for elem in &self.#field_ident {
                                    pack#push_fn(elem#pack_fn);
                                }
                            };
                            (array_enconding_length, field_packing)
                        }
                        Type::Path(ref _ty_path) => {
                            let enconding_length =
                                get_encoding_length_expression_of_type(&field.ty);
                            let (push_fn, pack_fn) = get_packing_function_of_type(&field.ty);
                            let field_packing = quote! {
                                pack#push_fn(self.#field_ident#pack_fn);
                            };
                            (enconding_length, field_packing)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };

                    if !encoding_length_expression.is_empty() {
                        encoding_length_expression.extend(quote! {+});
                    }
                    encoding_length_expression.extend(field_enconding_length);

                    packing.extend(field_packing);
                }
            }
            _ => abort_call_site!("only named fields are allowed!"),
        },
        _ => abort_call_site!("only struct types are allowed!"),
    }

    if encoding_length_expression.is_empty() {
        encoding_length_expression.extend(quote! {0});
    }

    let comma = Comma(Span::call_site());

    let mut function_generic_params = Punctuated::new();

    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    if has_engine_generic_param(&generics.params, &engine_generic_param) == false {
        function_generic_params.push(engine_generic_param.clone());
        function_generic_params.push_punct(comma.clone());
    }

    let cs_generic_param = syn::parse_str::<GenericParam>(&"CS: ConstraintSystem<E>").unwrap();
    function_generic_params.push(cs_generic_param.clone());
    function_generic_params.push_punct(comma.clone());

    let function_generics = Generics {
        lt_token: Some(syn::token::Lt(Span::call_site())),
        params: function_generic_params,
        gt_token: Some(syn::token::Gt(Span::call_site())),
        where_clause: None,
    };

    let expanded = quote! {
        #vis const #enconding_length_constant_ident: usize = #encoding_length_expression;

        impl#generics #ident<#type_params> {
            pub fn pack#function_generics(&self, cs: &mut CS) -> Result<[Num<E>; #enconding_length_constant_ident], SynthesisError> {
                let mut pack = Vec::new();

                #packing

                use std::convert::TryInto;
                Ok(pack.try_into().unwrap())
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
