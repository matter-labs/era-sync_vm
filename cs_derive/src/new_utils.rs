use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    punctuated::Punctuated, token::Comma, GenericArgument, GenericParam, Generics, PathArguments,
    Type, TypePath,
};

pub(crate) fn is_primitive(path_ty: &TypePath) -> bool {
    for p in ["u8", "u16", "u32", "u64", "u128"].iter() {
        if *path_ty == syn::parse_str::<TypePath>(p).unwrap() {
            return true;
        }
    }
    false
}

const EQUIVALENT_BASE_TYPES: [(&str, &str, &str, &str); 13] = [
    ("Num<E>", "E::Fr", "alloc", "get_value"),
    ("UInt256<E>", "BigUint", "alloc_from_biguint", "get_value"),
    ("UInt128<E>", "u128", "allocate", "get_value"),
    ("UInt64<E>", "u64", "allocate", "get_value"),
    ("UInt32<E>", "u32", "allocate", "get_value"),
    ("UInt16<E>", "u16", "allocate", "get_value"),
    ("UInt8<E>", "u8", "allocate", "get_value"),
    ("UInt160<E>", "u160", "allocate", "get_value"),
    ("Byte<E>", "u8", "from_u8_witness", "get_byte_value"),
    ("Boolean", "bool", "alloc", "get_value"),
    (
        "SmallFixedWidthInteger<E, U160>",
        "u160",
        "alloc_from_address_like",
        "get_value_address_like",
    ),
    (
        "SmallFixedWidthInteger<E, U32>",
        "u32",
        "from_u32_witness",
        "get_value_clamped",
    ),
    (
        "SmallFixedWidthInteger<E, W>",
        "E::Fr",
        "allocate",
        "get_value",
    ),
];

pub(crate) fn is_equivalent_of_base_type(path_ty: &TypePath) -> bool {
    for (base, _, _, _) in EQUIVALENT_BASE_TYPES.iter() {
        if *path_ty == syn::parse_str::<TypePath>(base).unwrap() {
            return true;
        }
    }
    false
}

pub(crate) fn is_base_type(path_ty: &TypePath) -> bool {
    for (_, base, _, _) in EQUIVALENT_BASE_TYPES.iter() {
        if *path_ty == syn::parse_str::<TypePath>(base).unwrap() {
            return true;
        }
    }
    false
}

pub(crate) fn get_equivalent_type(original_ty: &Type) -> Type {
    match original_ty {
        Type::Array(ty) => {
            let mut original_array_ty = ty.clone();
            let new_ty = get_equivalent_type(&ty.elem);
            original_array_ty.elem = Box::from(new_ty);

            Type::Array(original_array_ty)
        }
        Type::Path(ty) => {
            if let Some(base_type) = find_in_equivalent_base_types(ty) {
                Type::Path(base_type)
            } else {
                let mut witness_ident_str = String::from("<");
                witness_ident_str.push_str(&TokenStream::from(quote! {#ty}).to_string());
                witness_ident_str.push_str(" as ");
                let mut witnessed_ty = ty.clone();
                if let Some(last_seg) = witnessed_ty.path.segments.last_mut() {
                    let ident = last_seg.ident.clone();
                    let mut extended_seg_args =
                        if let PathArguments::AngleBracketed(args) = &last_seg.arguments {
                            args.args.clone()
                        } else {
                            Punctuated::new()
                        };
                    let mut engine_param_already_present = false;
                    for arg in &extended_seg_args {
                        if arg == &syn::parse_str("E").unwrap() {
                            engine_param_already_present = true;
                        }
                    }
                    if !engine_param_already_present {
                        extended_seg_args.insert(0, syn::parse_str("E").unwrap());
                    }

                    last_seg.ident =
                        syn::parse_str::<Ident>(&format!("{}CSWitnessed", ident)).unwrap();
                    last_seg.arguments = PathArguments::AngleBracketed(
                        syn::parse_str(&quote! {::<#extended_seg_args>}.to_string()).unwrap(),
                    );
                } else {
                    abort_call_site!("type path should contains a type")
                };
                witness_ident_str.push_str(&TokenStream::from(quote! {#witnessed_ty}).to_string());
                witness_ident_str.push_str(">::Witness");
                Type::Path(syn::parse_str::<TypePath>(&witness_ident_str).unwrap())
            }
        }
        _ => abort_call_site!("only array and path types are allowed"),
    }
}

fn find_in_equivalent_base_types(ty: &TypePath) -> Option<TypePath> {
    EQUIVALENT_BASE_TYPES
        .iter()
        .map(|(a, b, _, _)| {
            let first_ty: TypePath = syn::parse_str(a).unwrap();
            let second_ty: TypePath = syn::parse_str(b).unwrap();

            (first_ty, second_ty)
        })
        .find(|(a, _)| *a == *ty)
        .map(|(_, b)| b)
}

pub(crate) fn get_ident_of_field_type(ty: &Type) -> Ident {
    match ty {
        Type::Array(ref arr_ty) => get_ident_of_field_type(&arr_ty.elem),
        Type::Path(ref path_ty) => {
            if let Some(last_seg) = path_ty.path.segments.last() {
                last_seg.ident.clone()
            } else {
                abort_call_site!("type path should contains a type")
            }
        }
        _ => abort_call_site!("only array or path types are allowed"),
    }
}

pub(crate) fn get_type_path_of_field(ty: &Type) -> TypePath {
    match ty {
        Type::Array(ref arr_ty) => get_type_path_of_field(&arr_ty.elem),
        Type::Path(ref path_ty) => path_ty.clone(),
        _ => abort_call_site!("only array or path types are allowed"),
    }
}

pub(crate) fn get_base_type_allocation_fn_name_by_ident(ty: &TypePath) -> Option<Ident> {
    EQUIVALENT_BASE_TYPES
        .iter()
        .find(|(original_ident, _, _, _)| {
            syn::parse_str::<TypePath>(original_ident).unwrap() == *ty
        })
        .map(|(_, _, fn_str, _)| syn::parse_str(fn_str).unwrap())
    //    .expect(&format!("should find a matching 'allocation' fn name for {:?}", ty))
}

pub(crate) fn get_base_type_witness_fn_name_by_ident(ty: &TypePath) -> Option<Ident> {
    EQUIVALENT_BASE_TYPES
        .iter()
        .find(|(original_ident, _, _, _)| {
            syn::parse_str::<TypePath>(original_ident).unwrap() == *ty
        })
        .map(|(_, _, _, fn_str)| syn::parse_str(fn_str).unwrap())
    //    .expect(&format!("should find a matching 'get value' fn name for {:?}", ty))
}

pub(crate) fn has_engine_generic_param<P>(
    generic_params: &Punctuated<GenericParam, P>,
    param: &GenericParam,
) -> bool {
    for p in generic_params {
        if p == param {
            return true;
        }
    }
    return false;
}

pub(crate) fn get_type_params_from_generics<P: Clone + Default>(
    generics: &Generics,
    punc: &P,
    skip_engine: bool,
) -> Punctuated<Ident, P> {
    let type_params = generics.type_params();
    let const_params = generics.const_params();

    let mut idents = Punctuated::new();

    for param in type_params.into_iter() {
        if skip_engine && *param == syn::parse_str("E: Engine").unwrap() {
            continue;
        }
        let ident = param.ident.clone();
        idents.push(ident);
        idents.push_punct(punc.clone());
    }

    for param in const_params.into_iter() {
        let ident = param.ident.clone();
        idents.push(ident.clone());
        idents.push_punct(punc.clone());
    }

    idents
}

pub(crate) fn get_type_params_from_generics_output_params<P: Clone + Default>(
    generics: &Generics,
    punc: &P,
    skip_engine: bool,
) -> Punctuated<GenericParam, P> {
    let type_params = generics.type_params();
    let const_params = generics.const_params();

    let mut idents = Punctuated::new();

    for param in type_params.into_iter() {
        if skip_engine && *param == syn::parse_str("E: Engine").unwrap() {
            continue;
        }
        idents.push(GenericParam::Type(param.clone()));
        idents.push_punct(punc.clone());
    }

    for param in const_params.into_iter() {
        idents.push(GenericParam::Const(param.clone()));
        idents.push_punct(punc.clone());
    }

    idents
}

pub(crate) fn virually_monomorphize_type(ty: &TypePath) -> TypePath {
    let substitution_ty = syn::parse_str::<Type>("crate::pairing::bn256::Bn256").unwrap();
    let mut new_ty = ty.clone();
    for (idx, segment) in new_ty.path.segments.iter_mut().enumerate() {
        if idx > 0 {
            abort_call_site!("can not virtually monomorphize for type parameters other than Engine, that should be first");
        }
        match &mut segment.arguments {
            PathArguments::AngleBracketed(generics) => {
                for (i, arg) in generics.args.iter_mut().enumerate() {
                    if i > 0 {
                        abort_call_site!("can not virtually monomorphize for type parameters other than Engine, that should be first");
                    }
                    match arg {
                        GenericArgument::Type(ref mut t) => {
                            let mut change = false;
                            match t {
                                Type::Path(ref p) => {
                                    for (ii, pp) in p.path.segments.iter().enumerate() {
                                        if ii > 0 {
                                            abort_call_site!("can not virtually monomorphize for type parameters other than Engine, that should be first");
                                        }
                                        if *pp == syn::parse_str("E").unwrap() {
                                            change = true;
                                        }
                                    }
                                },
                                _ => abort_call_site!("can not virtually monomorphize for type parameters other than Engine, that should be first"),
                            }

                            if change {
                                *t = substitution_ty.clone();
                            }
                        }
                        _ => {
                            abort_call_site!("can not virtually monomorphize for type parameters other than Engine, that should be first");
                        }
                    }
                }
            }
            PathArguments::Parenthesized(..) => {
                abort_call_site!("can not virtually monomorphize for complex generics");
            }
            PathArguments::None => {}
        }
    }

    new_ty
}

pub(crate) fn virually_monomorphize(generics: &Generics) -> Ident {
    let type_params = generics.type_params();
    let const_params = generics.const_params();

    let mut formed_ident = None;

    for param in type_params.into_iter() {
        if *param == syn::parse_str("E: Engine").unwrap() {
            let ident = syn::parse_str("crate::pairing::bn256::Bn256").unwrap();
            formed_ident = Some(ident);
        } else {
            abort_call_site!(
                "can not virtually monomorphize for type parameters other than Engine"
            );
        }
    }

    for _param in const_params.into_iter() {
        abort_call_site!("can not virtually monomorphize for const generics involved");
    }

    formed_ident.unwrap()
}

pub(crate) fn get_witness_ident(original_ident: &Ident) -> Ident {
    let mut witness_ident_str = original_ident.to_string();
    witness_ident_str.push_str(&"Witness");
    syn::parse_str(&witness_ident_str).unwrap()
}

/// Fetch an attribute string from the derived struct.
pub(crate) fn fetch_attr(name: &str, attrs: &[syn::Attribute]) -> Option<String> {
    for attr in attrs {
        if let Ok(meta) = attr.parse_meta() {
            match meta {
                syn::Meta::NameValue(nv) => {
                    if nv.path.is_ident(name) {
                        match nv.lit {
                            syn::Lit::Str(ref s) => return Some(s.value()),
                            _ => {} // _ => panic!("attribute {} not found", name)
                        }
                    }
                }
                _ => {} // _ => panic!("attribute {} not found", name)
            }
        }
    }

    None
}

// we always need Engine here but there are some cases when original struct has no Engine param
// in its definition. e.g when original struct only has Boolean in its fields.
// we prepend here because we don't want to add E into type params while E should be in impl part
// e.g impl<E: Engine, const L: usize> Trait for Sturct<L>
pub(crate) fn prepend_engine_param_if_not_exist(generics: &mut Generics) {
    let mut new_generic_params = Punctuated::new();

    let engine_generic_param = syn::parse_str::<GenericParam>(&"E: Engine").unwrap();
    if has_engine_generic_param(&generics.params, &engine_generic_param) == false {
        new_generic_params.push(engine_generic_param.clone());
        new_generic_params.push_punct(Comma(Span::call_site()));
    }

    new_generic_params.extend(generics.params.clone());

    *generics = Generics {
        lt_token: Some(syn::token::Lt(Span::call_site())),
        params: new_generic_params,
        gt_token: Some(syn::token::Gt(Span::call_site())),
        where_clause: None,
    };
}

pub(crate) fn get_empty_path_field_initialization_of_type(ty: &TypePath) -> TokenStream {
    if ty == &syn::parse_str(&"bool").unwrap() {
        quote! {
            false
        }
    } else if is_primitive(ty) {
        quote! {
            0
        }
    } else if is_base_type(ty) {
        quote! {
            #ty::zero()
        }
    } else {
        quote! {
            #ty::empty()
        }
    }
}

pub(crate) fn get_empty_field_initialization_of_type(ty: &Type) -> TokenStream {
    match ty {
        syn::Type::Array(ref ty_arr) => {
            let len = &ty_arr.len;
            let field_init = get_empty_field_initialization_of_type(&ty_arr.elem);
            quote! {
                vec![#field_init; #len].try_into().unwrap()
            }
        }
        syn::Type::Path(ref y_path) => {
            let field_init = get_empty_path_field_initialization_of_type(y_path);
            quote! {
                #field_init
            }
        }
        _ => abort_call_site!("only array and path types are allowed"),
    }
}

pub(crate) fn get_empty_path_field_allocation_of_type(ty: &TypePath) -> TokenStream {
    let field_ident = get_ident_of_field_type(&Type::Path(ty.clone()));
    if is_equivalent_of_base_type(ty) {
        quote! {
            #field_ident::zero()
        }
    } else {
        quote! {
            #field_ident::empty()
        }
    }
}

pub(crate) fn get_empty_field_allocation_of_type(ty: &Type) -> TokenStream {
    match ty {
        syn::Type::Array(ref ty_arr) => {
            let len = &ty_arr.len;
            let field_empty = get_empty_field_allocation_of_type(&ty_arr.elem);
            quote! {
                [#field_empty; #len]
            }
        }
        syn::Type::Path(ref y_path) => {
            let field_empty = get_empty_path_field_allocation_of_type(y_path);
            quote! {
                #field_empty
            }
        }
        _ => abort_call_site!("only array and path types are allowed"),
    }
}

pub(crate) fn get_path_field_encoding_length_expression_of_type(ty: &TypePath) -> TokenStream {
    if is_equivalent_of_base_type(ty) {
        let field_ident = get_ident_of_field_type(&Type::Path(ty.clone()));
        if field_ident == syn::parse_str::<Ident>("UInt256").unwrap() {
            quote! {4}
        } else {
            quote! {1}
        }
    } else {
        let field_ident = get_ident_of_field_type(&Type::Path(ty.clone()));
        let extended_ident =
            syn::parse_str::<Ident>(&format!("{}CircuitEncodingLength", field_ident)).unwrap();
        quote! {
            #extended_ident
        }
    }
}

pub(crate) fn get_encoding_length_expression_of_type(ty: &Type) -> TokenStream {
    match ty {
        syn::Type::Array(ref ty_arr) => {
            let len = &ty_arr.len;
            let field_encoding_length = get_encoding_length_expression_of_type(&ty_arr.elem);
            quote! {
                #field_encoding_length * (#len)
            }
        }
        syn::Type::Path(ref y_path) => {
            let field_encoding_length = get_path_field_encoding_length_expression_of_type(y_path);
            quote! {
                #field_encoding_length
            }
        }
        _ => abort_call_site!("only array and path types are allowed"),
    }
}

pub(crate) fn get_path_field_packing_function_of_type(ty: &TypePath) -> (TokenStream, TokenStream) {
    let push_fn = TokenStream::from(quote! {.push});
    let extend_fn = TokenStream::from(quote! {.extend});

    if is_equivalent_of_base_type(ty) {
        let field_ident = get_ident_of_field_type(&Type::Path(ty.clone()));
        if field_ident == syn::parse_str::<Ident>("SmallFixedWidthInteger").unwrap() {
            (push_fn, quote! {.value})
        } else if field_ident == syn::parse_str::<Ident>("Num").unwrap() {
            (push_fn, quote! {})
        } else if field_ident == syn::parse_str::<Ident>("Boolean").unwrap() {
            (push_fn, quote! {.lc(E::Fr::one()).into_num(cs)?})
        } else if field_ident == syn::parse_str::<Ident>("UInt256").unwrap() {
            (extend_fn, quote! {.inner.iter().map(|elem| elem.inner)})
        } else {
            (push_fn, quote! {.inner})
        }
    } else {
        (extend_fn, quote! {.pack(cs)?})
    }
}

pub(crate) fn get_packing_function_of_type(ty: &Type) -> (TokenStream, TokenStream) {
    match ty {
        Type::Array(ref arr_ty) => get_packing_function_of_type(&arr_ty.elem),
        Type::Path(ref path_ty) => get_path_field_packing_function_of_type(path_ty),
        _ => abort_call_site!("only array or path types are allowed"),
    }
}
