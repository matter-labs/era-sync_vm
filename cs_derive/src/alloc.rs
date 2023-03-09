use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Comma, DeriveInput, GenericParam, Generics,
    Type, TypeArray, TypePath,
};

use crate::{
    utils::{
        get_allocation_fn_name_by_ident, get_ident_of_field_type, get_type_params_from_generics,
        get_type_path_of_field, get_witness_ident, has_engine_generic_param,
    },
    witness::derive_witness_struct,
};

fn derive_from_array(ident: &Ident, ty: &TypeArray) -> (TokenStream, TokenStream) {
    let len = &ty.len;
    let ty_arr = Type::Array(ty.clone());
    let ty_path = get_type_path_of_field(&ty_arr);
    let ty_ident = get_ident_of_field_type(&ty_arr);
    let fn_ident = get_allocation_fn_name_by_ident(&ty_path);

    let empty = quote! {
        let mut #ident = [#ty_ident::zero(); #len];
    };

    let alloc = quote! {
        if let Some(ref witness) = witness{
            for (allocated, wit) in #ident.iter_mut().zip(witness.#ident){
                *allocated = #ty_ident::#fn_ident(cs, Some(wit))?;
            }
        }
    };

    (empty, alloc)
}

fn derive_from_path(ident: &Ident, ty: &TypePath) -> (TokenStream, TokenStream) {
    let elem_ident = get_ident_of_field_type(&Type::Path(ty.clone()));
    let fn_ident = get_allocation_fn_name_by_ident(ty);
    let empty = quote! {
        let mut #ident = #elem_ident::zero();
    };
    let alloc = quote! {
        let mut #ident = #elem_ident::#fn_ident(cs, witness.as_ref().map(|w| w.#ident.clone()))?;
    };

    (empty, alloc)
}

pub(crate) fn derive_alloc(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);
    let DeriveInput {
        ident,
        generics,
        data,
        ..
    } = derived_input.clone();

    let mut struct_initializations = TokenStream::new();
    let mut array_initializations = TokenStream::new();
    let mut array_initializations_for_allocation = TokenStream::new();
    let mut field_initializations_for_allocation = TokenStream::new();
    let mut field_initializations_for_empty_fn = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("should have a field elem ident");
                    match field.ty {
                        Type::Array(ref array_ty) => {
                            let (array_init, alloc) = derive_from_array(&field_ident, array_ty);
                            array_initializations.extend(array_init);
                            array_initializations_for_allocation.extend(alloc);
                        }
                        Type::Path(ref ty_path) => {
                            let (empty, alloc) = derive_from_path(&field_ident, ty_path);
                            field_initializations_for_empty_fn.extend(empty);
                            field_initializations_for_allocation.extend(alloc);
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

    let witness_ident = get_witness_ident(&ident);
    let witness_struct = derive_witness_struct(derived_input);

    let comma = Comma(Span::call_site());

    let mut function_generic_params = Punctuated::new();

    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    if has_engine_generic_param(&generics.params, &engine_generic_param) == false
        && has_engine_generic_param(&witness_struct.generics.params, &engine_generic_param) == false
    {
        function_generic_params.push(engine_generic_param.clone());
        function_generic_params.push_punct(comma.clone());
    }

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

    let type_params_of_allocated_struct = get_type_params_from_generics(&generics, &comma, false);
    let type_params_of_witness_struct =
        get_type_params_from_generics(&witness_struct.generics, &comma, false);

    let expanded = quote! {
        impl#generics #ident<#type_params_of_allocated_struct>{
            pub fn allocate#function_generics(cs: &mut CS, witness: Option<#witness_ident<#type_params_of_witness_struct>>) -> Result<Self, SynthesisError>{
                #array_initializations
                #array_initializations_for_allocation
                #field_initializations_for_allocation

                Ok(Self{
                    #struct_initializations
                })
            }

            pub fn empty() -> Self{
                #array_initializations
                #field_initializations_for_empty_fn

                Self{
                    #struct_initializations
                }
            }
        }

        impl#generics Default for #ident<#type_params_of_allocated_struct>{
            fn default() -> Self{
                Self::empty()
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
