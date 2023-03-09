use crate::utils::{
    get_ident_of_field_type, get_type_params_from_generics, has_engine_generic_param,
};
use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, GenericParam, Type};

pub(crate) fn derive_eq(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        data,
        mut generics,
        ..
    } = derived_input.clone();

    let mut array_equality_check = TokenStream::new();
    let mut path_equality_check = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => {
            match struct_data.fields {
                syn::Fields::Named(ref named_fields) => {
                    let len = named_fields.named.len();
                    for (idx, field) in named_fields.named.iter().enumerate() {
                        let field_ident = field.ident.clone().expect("a field ident");
                        let ty_ident = get_ident_of_field_type(&field.ty);
                        let _is_bool = ty_ident == syn::parse_str::<Ident>("Boolean").unwrap();

                        let equality = match field.ty {
                            Type::Array(ref ty) => {
                                match *ty.elem {
                                    Type::Path(ref _p) => {}
                                    _ => abort_call_site!("only array of elements is allowed here"),
                                };

                                let eq = quote! {
                                    let #field_ident = self.#field_ident.iter().zip(other.#field_ident.iter()).map(|(t, o)| CircuitEq::<E>::eq(t, &o)).all(|r| r);
                                };

                                // let eq = if is_bool || !is_equivalent_of_base_type(&get_type_path_of_field(&ty.elem)){
                                //     quote!{
                                //         let #field_ident = self.#field_ident.iter().zip(other.#field_ident.iter()).map(|(t, o)| CircuitEq::<E>::eq(t, &o)).all(|r| r);
                                //     }
                                // }else{
                                //     quote! {
                                //         let #field_ident = self.#field_ident.iter().zip(other.#field_ident.iter()).map(|(t, o)| t.eq(&o)).all(|r| r);
                                //     }
                                // };

                                array_equality_check.extend(eq);
                                quote! {
                                    #field_ident
                                }
                            }
                            Type::Path(ref _ty) => {
                                quote! {
                                    CircuitEq::<E>::eq(&self.#field_ident, &other.#field_ident)
                                }

                                // if is_bool || !is_equivalent_of_base_type(&ty){
                                //     quote! {
                                //         CircuitEq::<E>::eq(&self.#field_ident, &other.#field_ident)
                                //     }
                                // }else{
                                //     quote! {
                                //         self.#field_ident.eq(&other.#field_ident)
                                //     }
                                // }
                            }
                            _ => abort_call_site!("only array and path types are allowed"),
                        };
                        path_equality_check.extend(equality);
                        if idx != len - 1 {
                            path_equality_check.extend(quote! {&&})
                        }
                    }
                }
                _ => abort_call_site!("only named fields are allowed"),
            }
        }
        _ => abort_call_site!("only data structs are allowed"),
    }

    let comma = Comma(Span::call_site());
    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    let has_engine_param = has_engine_generic_param(&generics.params, &engine_generic_param);
    if has_engine_param == false {
        generics.params.insert(0, engine_generic_param.clone());
    }

    let type_params_of_allocated_struct =
        get_type_params_from_generics(&generics, &comma, has_engine_param == false);

    let expanded = quote! {
        impl#generics CircuitEq<E> for #ident<#type_params_of_allocated_struct>{
            fn eq(&self, other: &Self) -> bool {
                #array_equality_check

                #path_equality_check
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
