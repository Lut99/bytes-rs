//  LIB.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:06:44
//  Last edited:
//    19 Sep 2023, 21:09:26
//  Auto updated?
//    Yes
// 
//  Description:
//!   Contributes the derive macros for the `bytes`-crate.
// 

mod try_from_bytes;


/***** LIBRARY *****/
/// See the auto-generated documentation at `ast_toolkit::procedural::Diagnostic` for more information.
#[proc_macro_error::proc_macro_error]
#[proc_macro_derive(TryFromBytes, attributes(try_from_bytes))]
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
