use crate::utils::{
    get_ident_of_field_type, get_type_params_from_generics, has_engine_generic_param,
};
use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, GenericParam, Type};

pub(crate) fn derive_ord(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        data,
        mut generics,
        ..
    } = derived_input.clone();

    let _array_equality_check = TokenStream::new();
    let mut path_equality_check = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                let _len = named_fields.named.len();
                for (_idx, field) in named_fields.named.iter().enumerate() {
                    let field_ident = field.ident.clone().expect("a field ident");
                    let ty_ident = get_ident_of_field_type(&field.ty);
                    let is_bool = ty_ident == syn::parse_str::<Ident>("Boolean").unwrap();

                    let equality = match field.ty {
                        Type::Array(_) | Type::Path(_) => {
                            if is_bool {
                                quote! {
                                    let ord = CircuitOrd::<E>::cmp(&self.#field_ident, &other.#field_ident);
                                    if ord != ::std::cmp::Ordering::Equal {return ord;}

                                }
                            } else {
                                quote! {
                                    let ord = CircuitOrd::<E>::cmp(&self.#field_ident, &other.#field_ident);
                                    if ord != ::std::cmp::Ordering::Equal {return ord;}

                                }
                            }
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    path_equality_check.extend(equality);
                }
            }
            _ => abort_call_site!("only named fields are allowed"),
        },
        _ => abort_call_site!("only data structs are allowed"),
    }

    let comma = Comma(Span::call_site());
    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    let has_engine_param = has_engine_generic_param(&generics.params, &engine_generic_param);
    if has_engine_param == false {
        generics.params.insert(0, engine_generic_param.clone());
        generics.params.push_punct(comma.clone());
    }

    let type_params_of_allocated_struct =
        get_type_params_from_generics(&generics, &comma, has_engine_param == false);

    let expanded = quote! {
        impl#generics CircuitOrd<E> for #ident<#type_params_of_allocated_struct>{
            fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
                // #array_equality_check

                #path_equality_check

                std::cmp::Ordering::Equal
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
