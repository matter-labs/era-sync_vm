use proc_macro2::{Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Comma, DeriveInput, GenericParam, Generics,
    Type,
};

use crate::utils::{
    get_ident_of_field_type, get_type_params_from_generics, has_engine_generic_param,
};

pub(crate) fn derive_orthogonal_select(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);
    let DeriveInput {
        ident,
        mut generics,
        data,
        ..
    } = derived_input.clone();

    let mut struct_initializations = TokenStream::new();
    let _array_selections = TokenStream::new();
    let mut field_selections = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("should have a field elem ident");
                    let _el_ty = get_ident_of_field_type(&field.ty);
                    match field.ty {
                        // Type::Array(_) => {
                        //     let field_select = quote! {
                        //         let this_ref = reference.#field_ident.clone();
                        //         let this_subset: Vec<_> = candidates.iter().map(|el| (el.0, el.1.#field_ident.clone())).collect();
                        //         let #field_ident = CircuitOrthogonalSelectable::<E>::select_update_assuming_orthogonality(cs, this_ref, &this_subset)?;
                        //     };
                        //     field_selections.extend(field_select);
                        // },
                        Type::Array(_) | Type::Path(_) => {
                            let field_select = quote! {
                                let this_ref = reference.#field_ident.clone();
                                let this_subset: Vec<_> = candidates.iter().map(|el| (el.0, el.1.#field_ident.clone())).collect();
                                let #field_ident = CircuitOrthogonalSelectable::<E>::select_update_assuming_orthogonality(cs, this_ref, &this_subset)?;
                            };
                            field_selections.extend(field_select);
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };

                    let init_field = quote! {
                        #field_ident,
                    };

                    struct_initializations.extend(init_field);
                }
            }
            _ => abort_call_site!("only named fields are allowed!"),
        },
        _ => abort_call_site!("only struct types are allowed!"),
    }

    let comma = Comma(Span::call_site());
    let mut function_generic_params = Punctuated::new();

    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    let has_engine_param = has_engine_generic_param(&generics.params, &engine_generic_param);
    if has_engine_param == false {
        generics.params.insert(0, engine_generic_param.clone());
        generics.params.push_punct(comma.clone());
    }

    let type_params_of_allocated_struct =
        get_type_params_from_generics(&generics, &comma, has_engine_param == false);

    // add CS to func generic params
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
        impl#generics CircuitOrthogonalSelectable<E> for #ident<#type_params_of_allocated_struct>{
            fn select_update_assuming_orthogonality#function_generics(cs: &mut CS, reference: Self, candidates: &[(Boolean, Self)]) -> Result<Self, SynthesisError> {
                // #array_selections
                #field_selections

                Ok(Self {
                    #struct_initializations
                })
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
