use proc_macro2::Span;
use syn::*;
use syn::{punctuated::Punctuated, GenericParam, Type, TypeArray, TypeParam, TypePath};

#[test]
fn test_type_path() {
    {
        let original_path: Path = syn::parse_str(&"E::Fr").unwrap();

        let mut expected_path = Path {
            leading_colon: None,
            segments: Punctuated::new(),
        };

        let first: PathSegment = syn::parse_str(&"E").unwrap();
        expected_path.segments.push_value(first);

        let colon: Token![::] = syn::parse_str(&"::").unwrap();
        expected_path.segments.push_punct(colon);

        let second: PathSegment = syn::parse_str(&"Fr").unwrap();
        expected_path.segments.push_value(second);

        assert_eq!(original_path, expected_path);
    }

    {
        let original_path: Path = syn::parse_str(&"Num<E>").unwrap();

        let mut expected_path = Path {
            leading_colon: None,
            segments: Punctuated::new(),
        };

        let first: PathSegment = syn::parse_str(&"Num<E>").unwrap();
        expected_path.segments.push_value(first);

        assert_eq!(original_path, expected_path);
    }
}

#[test]
fn test_type_array() {
    let original_arr: TypeArray = syn::parse_str(&"[E::Fr; 2]").unwrap();

    let expected_arr = TypeArray {
        bracket_token: syn::token::Bracket(Span::call_site()),
        elem: syn::parse_str::<Box<Type>>("E::Fr").unwrap(),
        semi_token: syn::token::Semi(Span::call_site()),
        len: syn::parse_str(&"2").unwrap(),
    };

    assert_eq!(original_arr, expected_arr);
}

#[test]
fn test_equivalent_type() {
    {
        let original_type = syn::parse_str::<Type>(&"Num<E>").unwrap();
        let expected_type = Type::Path(syn::parse_str::<TypePath>(&"E::Fr").unwrap());
        let expected_type_param = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param),
            actual_type_param.unwrap()
        );
    }

    {
        let original_type = syn::parse_str::<Type>(&"[Num<E>; 3]").unwrap();
        let expected_type = Type::Array(syn::parse_str(&"[E::Fr; 3]").unwrap());
        let expected_type_param = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param),
            actual_type_param.unwrap()
        );
    }
    {
        let original_type = syn::parse_str::<Type>(&"[[Num<E>; 2]]").unwrap();
        let expected_type = Type::Slice(syn::parse_str(&"[[E::Fr; 2]]").unwrap());
        let expected_type_param = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param),
            actual_type_param.unwrap()
        );
    }
    {
        let original_type = syn::parse_str::<Type>(&"[[Num<E>; 2]; 3]").unwrap();
        let expected_type = Type::Array(syn::parse_str(&"[[E::Fr; 2]; 3]").unwrap());
        let expected_type_param = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param),
            actual_type_param.unwrap()
        );
    }
    {
        let original_type =
            syn::parse_str::<Type>(&"[[SmallFixedInteger<E, U160>; 2]; 3]").unwrap();
        let expected_type = Type::Array(syn::parse_str(&"[[E::Fr; 2]; 3]").unwrap());
        let expected_type_param1 = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param1),
            actual_type_param.unwrap()
        );
    }

    {
        let original_type = syn::parse_str::<Type>(&"Vec<Num<E>>").unwrap();
        let expected_type = Type::Path(syn::parse_str(&"Vec<E::Fr>").unwrap());
        let expected_type_param = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param),
            actual_type_param.unwrap()
        );
    }
    {
        let original_type = syn::parse_str::<Type>(&"Vec<[Num<E>]>").unwrap();
        let expected_type = Type::Path(syn::parse_str(&"Vec<[E::Fr]>").unwrap());
        let expected_type_param = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param),
            actual_type_param.unwrap()
        );
    }
    {
        let original_type = syn::parse_str::<Type>(&"Vec<[[Num<E>; 3]]>").unwrap();
        let expected_type = Type::Path(syn::parse_str(&"Vec<[[E::Fr;3]]>").unwrap());
        let expected_type_param = syn::parse_str::<TypeParam>(&"E: Engine").unwrap();

        let (actual_type, actual_type_param) = crate::utils::get_equivalent_type(&original_type);
        assert_eq!(expected_type, actual_type);

        assert_eq!(
            GenericParam::Type(expected_type_param),
            actual_type_param.unwrap()
        );
    }
}
