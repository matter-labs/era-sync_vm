use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, token::Comma, Attribute, Data, DeriveInput, Field, Fields, GenericParam,
    Generics, Type, TypeArray, TypePath,
};

use crate::new_utils::get_type_params_from_generics_output_params;
use crate::new_utils::{
    get_type_params_from_generics, get_witness_ident, has_engine_generic_param,
};

const SERDE_REMOVE_BOUNDS: &'static str = "SerdeRemoveBounds";

pub(crate) fn derive_witnessable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        data,
        generics,
        attrs,
        ..
    } = derived_input.clone();

    let serde_remove_bounds = if let Some(serde_remove_bounds) =
        crate::new_utils::fetch_attr(SERDE_REMOVE_BOUNDS, &attrs)
    {
        let serde_remove_bounds =
            syn::parse_str::<syn::Expr>(&serde_remove_bounds).expect("has attr as Expr");

        serde_remove_bounds == syn::parse_str::<syn::Expr>("true").unwrap()
    } else {
        false
    };

    // let mut array_initializations = TokenStream::new();
    let mut witness_initializations = TokenStream::new();
    let mut placehodler_witness_initialization = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("a field ident");

                    let expanded_init_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_get_witness_by_type(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_get_witness_by_array_type(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    witness_initializations.extend(expanded_init_line);

                    let placeholder_init_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_placeholder_witness_by_type(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_placeholder_witness_by_array_type(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    placehodler_witness_initialization.extend(placeholder_init_line);
                }
            }
            _ => abort_call_site!("only named fields are allowed"),
        },
        _ => abort_call_site!("only data structs are allowed"),
    }

    let witness_ident = get_witness_ident(&ident);
    let witness_struct = derive_witness_struct_recursive(derived_input.clone());

    let comma = Comma(Span::call_site());

    let type_params_of_allocated_struct = get_type_params_from_generics(&generics, &comma, false);
    let type_params_of_witness_struct =
        get_type_params_from_generics(&witness_struct.generics, &comma, false);

    let where_clause = if let Some(clause) = generics.where_clause.as_ref() {
        quote! {
            #clause
        }
    } else {
        quote! {}
    };

    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    let _additional_engine_generic =
        if has_engine_generic_param(&generics.params, &engine_generic_param) {
            quote! {}
        } else {
            quote! {<E:Engine>}
        };

    let derive_line = if serde_remove_bounds {
        quote! {
            #[derive(Derivative, ::serde::Serialize, ::serde::Deserialize)]
            #[derivative(Clone, Debug, PartialEq(bound = ""), Eq(bound = ""))]
        }
    } else {
        quote! {
            #[derive(Derivative, ::serde::Serialize, ::serde::Deserialize)]
            #[serde(bound = "")]
            #[derivative(Clone, Debug, PartialEq(bound = ""), Eq(bound = ""))]
        }
    };

    let expanded = quote! {
        #derive_line
        #witness_struct

        impl#generics CSWitnessable<E> for #ident<#type_params_of_allocated_struct> #where_clause{
            type Witness = #witness_ident<#type_params_of_witness_struct>;

            fn create_witness(&self) -> Option<Self::Witness>{
                use num_traits::Zero;
                use std::convert::TryInto;
                // #array_initializations

                let witness = #witness_ident{
                    #witness_initializations

                    _marker: std::marker::PhantomData,
                };

                Some(witness)
            }

            fn placeholder_witness() -> Self::Witness {
                use num_traits::Zero;
                use std::convert::TryInto;
                // #array_initializations

                let witness = #witness_ident{
                    #placehodler_witness_initialization

                    _marker: std::marker::PhantomData,
                };

                witness
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn derive_get_witness_by_type(ident: &Ident, ty: &TypePath) -> TokenStream {
    quote! {
        #ident: <#ty as CSWitnessable<E>>::create_witness(&self.#ident)?,
    }
}

fn derive_get_witness_by_array_type(ident: &Ident, ty: &TypeArray) -> TokenStream {
    quote! {
        #ident: <#ty as CSWitnessable<E>>::create_witness(&self.#ident)?,
    }
}

fn derive_placeholder_witness_by_type(ident: &Ident, ty: &TypePath) -> TokenStream {
    quote! {
        #ident: <#ty as CSWitnessable<E>>::placeholder_witness(),
    }
}

fn derive_placeholder_witness_by_array_type(ident: &Ident, ty: &TypeArray) -> TokenStream {
    quote! {
        #ident: <#ty as CSWitnessable<E>>::placeholder_witness(),
    }
}

pub(crate) fn derive_witness_struct_recursive(derived_input: DeriveInput) -> DeriveInput {
    let DeriveInput {
        attrs: _attrs,
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
                        let (new_ty, derive_hint) = get_equivalent_type_recursive(&field.ty);
                        field.ty = new_ty;
                        match derive_hint {
                            SerdeDeriveToUse::Default => {
                                // let att: Attribute = syn::parse_quote! {
                                //     #[serde(bound = "")]
                                // };
                                // field.attrs.push(att);
                            }
                            SerdeDeriveToUse::BigArray => {
                                // let att: Attribute = syn::parse_quote! {
                                //     #[serde(bound = "", with = "::sync_vm::utils::BigArraySerde")]
                                // };
                                let att: Attribute = syn::parse_quote! {
                                    #[serde(with = "crate::utils::BigArraySerde")]
                                };
                                field.attrs.push(att);
                            }
                        }
                    }

                    let att_0: Attribute = syn::parse_quote! {
                        #[serde(skip)]
                    };
                    let att_1: Attribute = syn::parse_quote! {
                        #[serde(bound = "")]
                    };

                    let marker_field = Field {
                        attrs: vec![att_0, att_1],
                        vis: vis.clone(),
                        ident: Some(syn::parse_str("_marker").unwrap()),
                        colon_token: None,
                        ty: Type::Path(syn::parse_str("std::marker::PhantomData<E>").unwrap()),
                    };
                    fields.named.push(marker_field);
                }
                _ => abort_call_site!("only named fields are allowed"),
            }
        }
        _ => abort_call_site!("only structs are allowed"),
    };

    let punc_generic_params = get_type_params_from_generics_output_params(&generics, &comma, false);

    // let mut punc_generic_params = Punctuated::new();

    // punc_generic_params.push_value(syn::parse_str("E: Engine").unwrap());
    // punc_generic_params.push_punct(comma.clone());

    // for cp in generics.const_params() {
    //     punc_generic_params.push(GenericParam::Const(cp.clone()));
    //     // punc_generic_params.push_value(GenericParam::Const(cp.clone()));
    //     // punc_generic_params.push_punct(comma.clone());
    // }

    let new_generics = Generics {
        lt_token: generics.lt_token,
        params: punc_generic_params,
        gt_token: generics.gt_token,
        where_clause: generics.where_clause,
    };

    let witness_ident = get_witness_ident(&ident);

    DeriveInput {
        attrs: vec![],
        vis: vis,
        ident: witness_ident,
        generics: new_generics,
        data: data,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SerdeDeriveToUse {
    Default,
    BigArray,
}

// we assume that every type implements a trait
pub(crate) fn get_equivalent_type_recursive(original_ty: &Type) -> (Type, SerdeDeriveToUse) {
    match original_ty {
        Type::Array(ty) => {
            let ts = quote! {
                <#ty as CSWitnessable<E>>::Witness
            };
            let ts = proc_macro::TokenStream::from(ts);
            (
                Type::Path(syn::parse::<TypePath>(ts).unwrap()),
                SerdeDeriveToUse::BigArray,
            )
        }
        Type::Path(ty) => {
            let ts = quote! {
                <#ty as CSWitnessable<E>>::Witness
            };
            let ts = proc_macro::TokenStream::from(ts);
            (
                Type::Path(syn::parse::<TypePath>(ts).unwrap()),
                SerdeDeriveToUse::Default,
            )
        }
        _ => abort_call_site!("only array and path types are allowed"),
    }
}
