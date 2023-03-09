#![allow(dead_code)]

use proc_macro::TokenStream;

mod alloc;
mod eq;
mod fixed_decodable;
mod fixed_encodable;
mod get_witness;
mod ord;
mod orth_select;
mod select;
#[cfg(tests)]
mod tests;
mod utils;
mod witness;

mod new_alloc;
mod new_eq;
mod new_fixed_decodable;
mod new_fixed_encodable;
mod new_get_witness;
mod new_pack;
mod new_select;
mod new_utils;
mod new_witness;

#[proc_macro_derive(CSEqual)]
pub fn new_derive_eq(input: TokenStream) -> TokenStream {
    self::new_eq::derive_eq(input)
}

#[proc_macro_derive(CSSelectable)]
pub fn new_derive_select(input: TokenStream) -> TokenStream {
    self::new_select::derive_select(input)
}

#[proc_macro_derive(CSOrdering)]
pub fn derive_ord(input: TokenStream) -> TokenStream {
    self::ord::derive_ord(input)
}

#[proc_macro_derive(CSOrthogonalSelectable)]
pub fn derive_orthogonal_select(input: TokenStream) -> TokenStream {
    self::orth_select::derive_orthogonal_select(input)
}

#[proc_macro_derive(FixedLengthEncodableExt, attributes(EncodingLength, PackWithCS))]
pub fn derive_encodable(input: TokenStream) -> TokenStream {
    self::fixed_encodable::derive_encodable(input)
}
#[proc_macro_derive(FixedLengthDecodableExt, attributes(EncodingLength))]
pub fn derive_decodable(input: TokenStream) -> TokenStream {
    self::fixed_decodable::derive_decodable(input)
}

mod witnessable;
#[proc_macro_derive(CSWitnessable)]
pub fn derive_witnessable(input: TokenStream) -> TokenStream {
    self::witnessable::derive_witnessable(input)
}

mod allocatable;
#[proc_macro_derive(CSAllocatable)]
pub fn derive_allocatable(input: TokenStream) -> TokenStream {
    self::allocatable::derive_allocatable(input)
}

mod packable;
#[proc_macro_derive(CSPackable)]
pub fn derive_packable(input: TokenStream) -> TokenStream {
    let mut _ts = proc_macro2::TokenStream::new();
    let derived_input = self::packable::derive_packable(input, &mut _ts);

    derived_input
}

mod encodable;
#[proc_macro_derive(CSEncodable)]
pub fn derive_cs_encodable(input: TokenStream) -> TokenStream {
    let mut len_expr = proc_macro2::TokenStream::new();
    let _ = self::packable::derive_packable(input.clone(), &mut len_expr);

    self::encodable::derive_encodable(input, len_expr).into()
}

mod decodable;
#[proc_macro_derive(CSDecodable)]
pub fn derive_cs_decodable(input: TokenStream) -> TokenStream {
    let mut len_expr = proc_macro2::TokenStream::new();
    let _ = self::packable::derive_packable(input.clone(), &mut len_expr);

    self::decodable::derive_decodable(input, len_expr).into()
}

mod var_encodable;
#[proc_macro_derive(CSVariableLengthEncodable)]
pub fn derive_cs_var_encodable(input: TokenStream) -> TokenStream {
    let inner_impl: proc_macro2::TokenStream =
        self::packable::derive_var_packable(input.clone()).into();
    let outer_impl: proc_macro2::TokenStream =
        self::var_encodable::derive_var_encodable(input).into();

    let expanded = quote::quote! {
        #inner_impl

        #outer_impl
    };

    proc_macro::TokenStream::from(expanded).into()
}
