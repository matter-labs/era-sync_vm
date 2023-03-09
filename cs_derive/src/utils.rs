use proc_macro2::{Ident, Span};
use proc_macro_error::abort_call_site;
use syn::{
    punctuated::Punctuated, token::Comma, GenericParam, Generics, Type, TypeParam, TypePath,
};

const EQUIVALENT_TYPES: [(&str, &str, Option<&str>, &str, &str); 14] = [
    ("Num<E>", "E::Fr", Some("E: Engine"), "alloc", "get_value"),
    (
        "UInt256<E>",
        "BigUint",
        None,
        "alloc_from_biguint",
        "get_value",
    ),
    (
        "DecommitHash<E>",
        "BigUint",
        None,
        "alloc_from_witness",
        "create_witness",
    ),
    ("UInt128<E>", "u128", None, "allocate", "get_value"),
    ("UInt64<E>", "u64", None, "allocate", "get_value"),
    ("UInt32<E>", "u32", None, "allocate", "get_value"),
    ("UInt16<E>", "u16", None, "allocate", "get_value"),
    ("UInt8<E>", "u8", None, "allocate", "get_value"),
    ("UInt160<E>", "u160", None, "allocate", "get_value"),
    ("Byte<E>", "u8", None, "from_u8_witness", "get_byte_value"),
    ("Boolean", "bool", None, "alloc", "get_value"),
    (
        "SmallFixedWidthInteger<E, U160>",
        "u160",
        None,
        "alloc_from_address_like",
        "get_value_address_like",
    ),
    (
        "SmallFixedWidthInteger<E, U32>",
        "u32",
        None,
        "from_u32_witness",
        "get_value_clamped",
    ),
    (
        "SmallFixedWidthInteger<E, W>",
        "E::Fr",
        Some("E: Engine"),
        "allocate",
        "get_value",
    ),
];

pub(crate) fn get_equivalent_type(original_ty: &Type) -> (Type, Option<GenericParam>) {
    match original_ty {
        Type::Array(ty) => {
            let mut original_array_ty = ty.clone();
            let (new_ty, new_type_param) = get_equivalent_type(&ty.elem);
            original_array_ty.elem = Box::from(new_ty);

            (Type::Array(original_array_ty), new_type_param)
        }
        Type::Path(ty) => {
            let (new_ty, type_param) = find_in_equivalent_types(ty);

            (Type::Path(new_ty), type_param)
        }
        _ => abort_call_site!("only array and path types are allowed"),
    }
}

fn find_in_equivalent_types(ty: &TypePath) -> (TypePath, Option<GenericParam>) {
    EQUIVALENT_TYPES
        .iter()
        .map(|(a, b, c, _, _)| {
            let first_ty: TypePath = syn::parse_str(a).unwrap();
            let second_ty: TypePath = syn::parse_str(b).unwrap();
            let type_param = if let Some(ref ty_param) = c {
                Some(GenericParam::Type(
                    syn::parse_str::<TypeParam>(ty_param.clone()).unwrap(),
                ))
            } else {
                None
            };

            (first_ty, second_ty, type_param)
        })
        .find(|(a, _, _)| *a == *ty)
        .map(|(_, b, c)| (b, c))
        .expect("some field(s) have unknown type")
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

pub(crate) fn get_allocation_fn_name_by_ident(ty: &TypePath) -> Ident {
    EQUIVALENT_TYPES
        .iter()
        .find(|(original_ident, _, _, _, _)| {
            syn::parse_str::<TypePath>(original_ident).unwrap() == *ty
        })
        .map(|(_, _, _, fn_str, _)| syn::parse_str(fn_str).unwrap())
        .expect(&format!(
            "should find a matching 'allocation' fn name for {:?}",
            ty
        ))
}

pub(crate) fn get_witness_fn_name_by_ident(ty: &TypePath) -> Ident {
    EQUIVALENT_TYPES
        .iter()
        .find(|(original_ident, _, _, _, _)| {
            syn::parse_str::<TypePath>(original_ident).unwrap() == *ty
        })
        .map(|(_, _, _, _, fn_str)| syn::parse_str(fn_str).unwrap())
        .expect(&format!(
            "should find a matching 'get value' fn name for {:?}",
            ty
        ))
    // .expect("should find a matching 'get value' fn name")
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
                            _ => panic!("attribute {} not found", name),
                        }
                    }
                }
                _ => panic!("attribute {} not found", name),
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
