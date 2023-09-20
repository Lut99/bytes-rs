//  LIB.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:06:44
//  Last edited:
//    20 Sep 2023, 18:01:28
//  Auto updated?
//    Yes
// 
//  Description:
//!   Contributes the derive macros for the `bytes`-crate.
// 

mod common;
mod try_from_bytes;
mod try_from_bytes_dynamic;


/***** LIBRARY *****/
/// See the auto-generated documentation at `ast_toolkit::procedural::Diagnostic` for more information.
#[proc_macro_error::proc_macro_error]
#[proc_macro_derive(TryFromBytes, attributes(bytes))]
pub fn derive_try_from_bytes(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use syn::{parse_macro_input, DeriveInput};


    // Parse the thing we've gotten
    let DeriveInput{ ident, data, attrs, generics, vis } = parse_macro_input!(input);

    // Pass to the main function
    match try_from_bytes::derive(ident, data, attrs, generics, vis) {
        Ok(stream) => stream,
        Err(err)   => { err.abort(); },
    }
}



/// See the auto-generated documentation at `ast_toolkit::procedural::Diagnostic` for more information.
#[proc_macro_error::proc_macro_error]
#[proc_macro_derive(TryFromBytesDynamic, attributes(bytes))]
pub fn derive_try_from_bytes_dynamic(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use syn::{parse_macro_input, DeriveInput};


    // Parse the thing we've gotten
    let DeriveInput{ ident, data, attrs, generics, vis } = parse_macro_input!(input);

    // Pass to the main function
    match try_from_bytes_dynamic::derive(ident, data, attrs, generics, vis) {
        Ok(stream) => stream,
        Err(err)   => { err.abort(); },
    }
}
