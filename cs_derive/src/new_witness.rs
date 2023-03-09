use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Comma, Data, DeriveInput, Field, Fields,
    GenericParam, Generics, Type,
};

use crate::new_utils::{
    get_empty_field_initialization_of_type, get_equivalent_type, get_type_params_from_generics,
    get_witness_ident,
};

pub(crate) fn derive_witness(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let derived_input = derive_witness_struct(input.clone());
    let derived_witnessed_impl = derive_witnessed_impl(input);
    let derived_empty_fn = derive_empty_fn(&derived_input);
    let derived_default_impl = derive_default_impl(&derived_input);

    let expanded = quote! {
        #[derive(Derivative)]
        #[derivative(Clone, Debug)]
        #derived_input

        #derived_witnessed_impl

        #derived_empty_fn

        #derived_default_impl
    };

    TokenStream::from(expanded).into()
}

pub(crate) fn derive_witness_struct(derived_input: DeriveInput) -> DeriveInput {
    let DeriveInput {
        vis,
        ident,
        generics,
        mut data,
        ..
    } = derived_input;

    let comma = Comma(Span::call_site());

    match data {
        Data::Struct(ref mut struct_data) => {
            match struct_data.fields {
                // we only use named fields for now
                Fields::Named(ref mut fields) => {
                    for field in fields.named.iter_mut() {
                        let new_ty = get_equivalent_type(&field.ty);
                        field.ty = new_ty;
                    }

                    let marker_field = Field {
                        attrs: Vec::new(),
                        vis: vis.clone(),
                        ident: Some(syn::parse_str("_marker").unwrap()),
                        colon_token: None,
                        ty: Type::Path(syn::parse_str("std::marker::PhantomData<E>").unwrap()),
                    };
                    fields.named.push_value(marker_field);
                }
                _ => abort_call_site!("only named fields are allowed"),
            }
        }
        _ => abort_call_site!("only structs are allowed"),
    };

    let mut punc_generic_params = Punctuated::new();

    punc_generic_params.push_value(syn::parse_str("E: Engine").unwrap());
    punc_generic_params.push_punct(comma.clone());

    for cp in generics.const_params() {
        punc_generic_params.push_value(GenericParam::Const(cp.clone()));
        punc_generic_params.push_punct(comma.clone());
    }

    let new_generics = Generics {
        lt_token: generics.lt_token,
        params: punc_generic_params,
        gt_token: generics.gt_token,
        where_clause: None,
    };

    let witness_ident = get_witness_ident(&ident);

    DeriveInput {
        attrs: Vec::new(),
        vis: vis,
        ident: witness_ident,
        generics: new_generics,
        data: data,
    }
}

fn derive_witnessed_impl(derived_input: DeriveInput) -> TokenStream {
    let ident = &derived_input.ident;
    let witness_ident = get_witness_ident(&ident);
    let generics = &derived_input.generics;
    let type_params = get_type_params_from_generics(generics, &Comma(Span::call_site()), false);
    let mut type_params_witness =
        get_type_params_from_generics(generics, &Comma(Span::call_site()), true);
    type_params_witness.insert(0, syn::parse_str("E").unwrap());

    let witnessed_ident = syn::parse_str::<Ident>(&format!("{}CSWitnessed", ident)).unwrap();

    let comma = Comma(Span::call_site());
    let mut extended_generic_params = Punctuated::new();
    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    extended_generic_params.push(engine_generic_param.clone());
    extended_generic_params.push_punct(comma.clone());
    for cp in generics.const_params() {
        extended_generic_params.push_value(GenericParam::Const(cp.clone()));
        extended_generic_params.push_punct(comma.clone());
    }

    let extended_generics = Generics {
        lt_token: Some(syn::token::Lt(Span::call_site())),
        params: extended_generic_params,
        gt_token: Some(syn::token::Gt(Span::call_site())),
        where_clause: None,
    };

    quote! {
        pub trait #witnessed_ident#extended_generics {
            type Witness: Clone + std::fmt::Debug;
        }
        impl#extended_generics #witnessed_ident<#type_params_witness> for #ident<#type_params>{
            type Witness = #witness_ident<#type_params_witness>;
        }
    }
}

fn derive_empty_fn(input: &DeriveInput) -> TokenStream {
    let DeriveInput {
        generics,
        ident,
        data,
        ..
    } = input.clone();

    let mut field_initializations = TokenStream::new();

    match data {
        Data::Struct(ref struct_data) => match struct_data.fields {
            Fields::Named(ref fields) => {
                for field in fields.named.iter() {
                    let field_ident = field.ident.clone().expect("a field ident");
                    let empty_initialization =
                        if field_ident == syn::parse_str::<Ident>("_marker").unwrap() {
                            quote! {
                                _marker: std::marker::PhantomData,
                            }
                        } else {
                            let field_init = get_empty_field_initialization_of_type(&field.ty);
                            quote! {
                                #field_ident: #field_init,
                            }
                        };
                    field_initializations.extend(empty_initialization);
                }
            }
            _ => abort_call_site!("only named fields are allowed"),
        },
        _ => abort_call_site!("only structs are allowed"),
    };

    let type_params = get_type_params_from_generics(&generics, &Comma(Span::call_site()), false);

    quote! {
        impl#generics #ident<#type_params> {
            pub fn empty() -> Self{
                use num_traits::Zero;
                use std::convert::TryInto;
                Self{
                    #field_initializations
                }
            }
        }
    }
}

fn derive_default_impl(derived_input: &DeriveInput) -> TokenStream {
    let ident = &derived_input.ident;
    let generics = &derived_input.generics;
    let type_params = get_type_params_from_generics(generics, &Comma(Span::call_site()), false);

    quote! {
        impl#generics Default for #ident<#type_params>{
            fn default() -> Self{
                Self::empty()
            }
        }
    }
}
