use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, GenericParam, Type, TypeArray, TypePath};

use crate::new_utils::{get_type_params_from_generics, has_engine_generic_param};

pub(crate) fn derive_allocatable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = derived_input.clone();

    let mut allocations = TokenStream::new();
    let mut initializations = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("a field ident");

                    let allocation_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_allocate_by_type_path(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_allocate_by_array_type(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    allocations.extend(allocation_line);

                    initializations.extend(quote! {
                        #field_ident,
                    });
                }
            }
            _ => abort_call_site!("only named fields are allowed"),
        },
        _ => abort_call_site!("only data structs are allowed"),
    }

    let comma = Comma(Span::call_site());

    let type_params_of_allocated_struct = get_type_params_from_generics(&generics, &comma, false);

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

    let expanded = quote! {
        impl#generics CSAllocatable<E> for #ident<#type_params_of_allocated_struct> #where_clause {
            fn alloc_from_witness<CS: ConstraintSystem<E>>(cs: &mut CS, witness: Option<Self::Witness>) -> Result<Self, SynthesisError> {
                #allocations

                let new = Self {
                    #initializations
                };

                Ok(new)
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn derive_allocate_by_type_path(ident: &Ident, ty: &TypePath) -> TokenStream {
    // create a witness element
    quote! {
        let wit = witness.as_ref().map(|el| &el.#ident).cloned();
        let #ident = <#ty as CSAllocatable<E>>::alloc_from_witness(cs, wit)?;
    }
}

fn derive_allocate_by_array_type(ident: &Ident, ty: &TypeArray) -> TokenStream {
    quote! {
        let wit = witness.as_ref().map(|el| &el.#ident).cloned();
        let #ident = <#ty as CSAllocatable<E>>::alloc_from_witness(cs, wit)?;
    }
}
