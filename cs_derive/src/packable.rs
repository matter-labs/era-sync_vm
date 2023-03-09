use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, GenericParam, Type, TypeArray, TypePath};

use crate::new_utils::{
    get_type_params_from_generics, has_engine_generic_param, virually_monomorphize_type,
};

pub(crate) fn derive_packable(
    input: proc_macro::TokenStream,
    len_ts: &mut TokenStream,
) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = derived_input.clone();

    let mut packing = TokenStream::new();

    let mut len_expression = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("a field ident");

                    let packing_line = match field.ty {
                        Type::Path(ref _path_ty) => derive_by_type_path(&field_ident, _path_ty),
                        Type::Array(ref _arr_ty) => derive_by_array_type(&field_ident, _arr_ty),
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    packing.extend(packing_line);

                    let len_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            if let Some(len) = length_encodable_meta(_path_ty) {
                                quote! {
                                    #len
                                }
                            } else {
                                quote! {
                                    <#_path_ty>::CIRCUIT_ENCODING_LEN
                                }
                            }
                        }
                        Type::Array(ref _arr_ty) => create_array_len_extression_recursive(_arr_ty),
                        _ => abort_call_site!("only array and path types are allowed"),
                    };

                    if len_expression.is_empty() {
                        len_expression.extend(len_line);
                    } else {
                        len_expression.extend(quote! {+});
                        len_expression.extend(len_line);
                    }
                }
            }
            _ => abort_call_site!("only named fields are allowed"),
        },
        _ => abort_call_site!("only data structs are allowed"),
    }

    let comma = Comma(Span::call_site());

    let type_params_of_allocated_struct = get_type_params_from_generics(&generics, &comma, false);

    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    let _additional_engine_generic =
        if has_engine_generic_param(&generics.params, &engine_generic_param) {
            quote! {}
        } else {
            quote! {<E:Engine>}
        };

    let inner_const_ident =
        syn::parse_str::<Ident>(&format!("__{}_circuit_packing_len_inner", ident).to_lowercase())
            .unwrap();
    let private_mod_ident =
        syn::parse_str::<Ident>(&format!("__{}_private_consts_packable", ident).to_lowercase())
            .unwrap();

    let expanded = quote! {
        impl#generics #ident<#type_params_of_allocated_struct>{
            pub const CIRCUIT_ENCODING_LEN: usize = #len_expression;
        }

        mod #private_mod_ident {
            use super::*;

            type E = crate::bellman::pairing::bn256::Bn256;
            pub(crate) const #inner_const_ident: usize = #len_expression;
        }

        pub(crate) const #inner_const_ident: usize = self::#private_mod_ident::#inner_const_ident;

        // impl#generics CSPackable<E, {Self::CIRCUIT_ENCODING_LEN}> for #ident<#type_params_of_allocated_struct>{
        impl#generics CSPackable<E, {#inner_const_ident}> for #ident<#type_params_of_allocated_struct>{
            fn pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<[Num<E>; #inner_const_ident], SynthesisError> {
                use std::convert::TryInto;

                let mut tmp = vec![];

                #packing

                let result: [Num<E>; #inner_const_ident] = match tmp.try_into() {
                    Ok(res) => res,
                    Err(..) => unreachable!()
                };

                Ok(result)
            }
        }
    };

    *len_ts = len_expression;

    proc_macro::TokenStream::from(expanded)
}

pub(crate) fn derive_var_packable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = derived_input.clone();

    let mut packing = TokenStream::new();

    let mut len_expression = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("a field ident");

                    let packing_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_by_type_path_variable_length(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_by_array_variable_length(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    packing.extend(packing_line);

                    let len_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            if let Some(len) = length_encodable_meta(_path_ty) {
                                quote! {
                                    #len
                                }
                            } else {
                                quote! {
                                    <#_path_ty as CircuitVariableLengthEncodable<E>>::encoding_length()
                                }
                            }
                        }
                        Type::Array(ref _arr_ty) => {
                            create_array_len_extression_recursive_for_var_length(_arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };

                    if len_expression.is_empty() {
                        len_expression.extend(len_line);
                    } else {
                        len_expression.extend(quote! {+});
                        len_expression.extend(len_line);
                    }
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
        impl#generics #ident<#type_params_of_allocated_struct> #where_clause {
            fn variable_length_packing_length() -> usize {
                #len_expression
            }

            fn variable_length_pack<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> {
                let mut tmp = vec![];

                #packing

                Ok(tmp)
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

fn derive_by_type_path(ident: &Ident, _ty: &TypePath) -> TokenStream {
    quote! {
        let packed = self.#ident.pack(cs)?;
        tmp.extend(packed);
    }
}

fn derive_by_type_path_variable_length(ident: &Ident, _ty: &TypePath) -> TokenStream {
    quote! {
        let packed = CircuitVariableLengthEncodable::encode(&self.#ident, cs)?;
        tmp.extend(packed);
    }
}

// even though we have derived packing for types that pack into 1 element,
// current limitations require us to use a loop here
fn derive_by_array_type(ident: &Ident, _ty: &TypeArray) -> TokenStream {
    quote! {
        for el in self.#ident.iter() {
            let packed = el.pack(cs)?;
            tmp.extend(packed);
        }
    }
}

fn derive_by_array_variable_length(ident: &Ident, _ty: &TypeArray) -> TokenStream {
    quote! {
        for el in self.#ident.iter() {
            let packed = CircuitVariableLengthEncodable::encode(el, cs)?;
            tmp.extend(packed);
        }
    }
}

pub(crate) fn length_encodable_meta(path_ty: &TypePath) -> Option<usize> {
    for (p, len) in [("Num<E>", 1), ("Boolean", 1), ("Byte<E>", 1)].iter() {
        if *path_ty == syn::parse_str::<TypePath>(p).unwrap() {
            return Some(*len);
        }
    }
    None
}

fn create_array_len_extression_recursive(ty: &TypeArray) -> TokenStream {
    let mut stream = TokenStream::new();
    let base_ty = &ty.elem;
    let len_expr = &ty.len;
    match **base_ty {
        Type::Path(ref _ty) => {
            let sublen = if let Some(len) = length_encodable_meta(_ty) {
                quote! {
                    #len * #len_expr
                }
            } else {
                quote! {
                    <#_ty>::CIRCUIT_ENCODING_LEN * #len_expr
                }
            };

            stream.extend(sublen);
        }
        Type::Array(ref _array_ty) => {
            let substream = create_array_len_extression_recursive(_array_ty);
            let tmp = quote! {
                (#substream) * #len_expr
            };
            stream.extend(tmp);
        }
        _ => abort_call_site!("only arrays and types are supported"),
    };

    stream
}

fn create_array_len_extression_recursive_for_var_length(ty: &TypeArray) -> TokenStream {
    let mut stream = TokenStream::new();
    let base_ty = &ty.elem;
    let len_expr = &ty.len;
    match **base_ty {
        Type::Path(ref _ty) => {
            let sublen = if let Some(len) = length_encodable_meta(_ty) {
                quote! {
                    #len * #len_expr
                }
            } else {
                quote! {
                    <#_ty as CircuitVariableLengthEncodable<E>>::encoding_length() * #len_expr
                }
            };

            stream.extend(sublen);
        }
        Type::Array(ref _array_ty) => {
            let substream = create_array_len_extression_recursive_for_var_length(_array_ty);
            let tmp = quote! {
                (#substream) * #len_expr
            };
            stream.extend(tmp);
        }
        _ => abort_call_site!("only arrays and types are supported"),
    };

    stream
}

fn create_array_len_extression_recursive_monomorphized(ty: &TypeArray) -> TokenStream {
    let mut stream = TokenStream::new();
    let base_ty = &ty.elem;
    let len_expr = &ty.len;
    match **base_ty {
        Type::Path(ref _ty) => {
            let sublen = if let Some(len) = length_encodable_meta(_ty) {
                quote! {
                    #len * #len_expr
                }
            } else {
                let monomorphized_ty = virually_monomorphize_type(_ty);
                quote! {
                    <#monomorphized_ty>::CIRCUIT_ENCODING_LEN * #len_expr
                }
            };

            stream.extend(sublen);
        }
        Type::Array(ref _array_ty) => {
            let substream = create_array_len_extression_recursive(_array_ty);
            let tmp = quote! {
                (#substream) * #len_expr
            };
            stream.extend(tmp);
        }
        _ => abort_call_site!("only arrays and types are supported"),
    };

    stream
}
