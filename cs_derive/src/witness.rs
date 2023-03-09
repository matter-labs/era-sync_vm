use proc_macro2::{Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Comma, Data, DeriveInput, Fields,
    GenericParam, Generics, Type,
};

use crate::{
    get_witness::is_primitive,
    utils::{get_type_params_from_generics, get_type_path_of_field, get_witness_ident},
};

fn get_initialization_of_type(ty: &Type) -> TokenStream {
    let ty_ident = get_type_path_of_field(ty);

    if ty_ident == syn::parse_str(&"bool").unwrap() {
        quote! {
            false
        }
    } else if is_primitive(&ty_ident) {
        quote! {
            0
        }
    } else {
        quote! {
            #ty_ident::zero()
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
                    let field_init = get_initialization_of_type(&field.ty);
                    let empty_initialization = match field.ty {
                        syn::Type::Array(ref ty_arr) => {
                            let len = &ty_arr.len;
                            quote! {
                                #field_ident: [#field_init; #len],
                            }
                        }
                        syn::Type::Path(_) => quote! {#field_ident: #field_init,},
                        _ => abort_call_site!(""),
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
                Self{
                    #field_initializations
                }
            }
        }
    }
}

pub(crate) fn derive_witness(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = derive_witness_struct(parse_macro_input!(input as DeriveInput));
    let derived_empty_fn = derive_empty_fn(&derived_input);
    let derived_default_impl = derive_default_impl(&derived_input);

    let expanded = quote! {
        #[derive(Derivative)]
        #[derivative(Clone, Debug)]
        #derived_input

        #derived_empty_fn

        #derived_default_impl
    };

    TokenStream::from(expanded).into()
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

pub(crate) fn derive_witness_struct(derived_input: DeriveInput) -> DeriveInput {
    let DeriveInput {
        vis,
        ident,
        generics,
        mut data,
        ..
    } = derived_input;

    let comma = Comma(Span::call_site());

    let mut engine_generic_param = None;

    match data {
        Data::Struct(ref mut struct_data) => {
            match struct_data.fields {
                // we only use named fields for now
                Fields::Named(ref mut fields) => {
                    for field in fields.named.iter_mut() {
                        let (new_ty, some_engine_gp) = super::utils::get_equivalent_type(&field.ty);
                        field.ty = new_ty;
                        if let Some(gp) = some_engine_gp {
                            engine_generic_param = Some(gp)
                        }
                    }
                }
                _ => abort_call_site!("only named fields are allowed"),
            }
        }
        _ => abort_call_site!("only structs are allowed"),
    };

    let mut punc_generic_params = Punctuated::new();

    // if there is E: Engine generic param then push into type params
    if let Some(generic_param) = engine_generic_param {
        punc_generic_params.push_value(generic_param);
        punc_generic_params.push_punct(comma.clone());
    }

    // we use constant params as they are
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
