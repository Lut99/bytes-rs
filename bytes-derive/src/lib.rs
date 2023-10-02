//  LIB.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 14:10:57
//  Last edited:
//    02 Oct 2023, 20:43:14
//  Auto updated?
//    Yes
// 
//  Description:
//!   Implements the derive macro's part of the `bytes`-crate.
// 

// Declare the submodules
mod generate;
mod parse;
mod spec;


/***** LIBRARY *****/
/// See the documentation at `bytes::procedural::TryFromBytes` for more information.
#[proc_macro_error::proc_macro_error]
#[proc_macro_derive(TryFromBytes, attributes(bytes))]
pub fn derive_try_from_bytes(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro_error::{Diagnostic, Level};
    use syn::{parse_macro_input, Data, DataStruct, DeriveInput};
    use spec::TryFromBytesDynamicInfo;


    // Parse the thing we've gotten
    let DeriveInput{ ident, data, attrs, generics, vis: _ } = parse_macro_input!(input);
    let data: DataStruct = match data {
        Data::Struct(data) => data,
        Data::Enum(e)      => { Diagnostic::spanned(e.enum_token.span, Level::Error, "Can only derive TryFromBytes on structs, not enums".into()).abort(); },
        Data::Union(u)     => { Diagnostic::spanned(u.union_token.span, Level::Error, "Can only derive TryFromBytes on structs, not enums".into()).abort(); },
    };

    // Parse the input
    let info: TryFromBytesDynamicInfo = match parse::parse_parser(attrs, ident, data, false) {
        Ok(info) => info,
        Err(err) => { err.abort(); },
    };

    // Generate the code
    generate::generate_parser(generics, info).into()
}

/// See the documentation at `bytes::procedural::TryFromBytesDynamic` for more information.
#[proc_macro_error::proc_macro_error]
#[proc_macro_derive(TryFromBytesDynamic, attributes(bytes))]
pub fn derive_try_from_bytes_dynamic(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro_error::{Diagnostic, Level};
    use syn::{parse_macro_input, Data, DataStruct, DeriveInput};
    use spec::TryFromBytesDynamicInfo;


    // Parse the thing we've gotten
    let DeriveInput{ ident, data, attrs, generics, vis: _ } = parse_macro_input!(input);
    let data: DataStruct = match data {
        Data::Struct(data) => data,
        Data::Enum(e)      => { Diagnostic::spanned(e.enum_token.span, Level::Error, "Can only derive TryFromBytesDynamic on structs, not enums".into()).abort(); },
        Data::Union(u)     => { Diagnostic::spanned(u.union_token.span, Level::Error, "Can only derive TryFromBytesDynamic on structs, not enums".into()).abort(); },
    };

    // Parse the input
    let info: TryFromBytesDynamicInfo = match parse::parse_parser(attrs, ident, data, true) {
        Ok(info) => info,
        Err(err) => { err.abort(); },
    };

    // Generate the code
    generate::generate_parser(generics, info).into()
}



/// See the documentation at `bytes::procedural::TryFromBytes` for more information.
#[proc_macro_error::proc_macro_error]
#[proc_macro_derive(TryToBytes, attributes(bytes))]
pub fn derive_try_to_bytes(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro_error::{Diagnostic, Level};
    use syn::{parse_macro_input, Data, DataStruct, DeriveInput};
    use spec::TryToBytesDynamicInfo;


    // Parse the thing we've gotten
    let DeriveInput{ ident, data, attrs, generics, vis: _ } = parse_macro_input!(input);
    let data: DataStruct = match data {
        Data::Struct(data) => data,
        Data::Enum(e)      => { Diagnostic::spanned(e.enum_token.span, Level::Error, "Can only derive TryFromBytes on structs, not enums".into()).abort(); },
        Data::Union(u)     => { Diagnostic::spanned(u.union_token.span, Level::Error, "Can only derive TryFromBytes on structs, not enums".into()).abort(); },
    };

    // Parse the input
    let info: TryToBytesDynamicInfo = match parse::parse_serializer(attrs, ident, data, false) {
        Ok(info) => info,
        Err(err) => { err.abort(); },
    };

    // Generate the code
    generate::generate_serializer(generics, info).into()
}

/// See the documentation at `bytes::procedural::TryFromBytesDynamic` for more information.
#[proc_macro_error::proc_macro_error]
#[proc_macro_derive(TryToBytesDynamic, attributes(bytes))]
pub fn derive_try_to_bytes_dynamic(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro_error::{Diagnostic, Level};
    use syn::{parse_macro_input, Data, DataStruct, DeriveInput};
    use spec::TryToBytesDynamicInfo;


    // Parse the thing we've gotten
    let DeriveInput{ ident, data, attrs, generics, vis: _ } = parse_macro_input!(input);
    let data: DataStruct = match data {
        Data::Struct(data) => data,
        Data::Enum(e)      => { Diagnostic::spanned(e.enum_token.span, Level::Error, "Can only derive TryFromBytesDynamic on structs, not enums".into()).abort(); },
        Data::Union(u)     => { Diagnostic::spanned(u.union_token.span, Level::Error, "Can only derive TryFromBytesDynamic on structs, not enums".into()).abort(); },
    };

    // Parse the input
    let info: TryToBytesDynamicInfo = match parse::parse_serializer(attrs, ident, data, true) {
        Ok(info) => info,
        Err(err) => { err.abort(); },
    };

    // Generate the code
    generate::generate_serializer(generics, info).into()
}
