//  TRY FROM BYTES.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:09:49
//  Last edited:
//    21 Sep 2023, 13:14:34
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the derivation procedure for the [`TryFromBytes`].
// 

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use proc_macro_error::{Diagnostic, Level};
use syn::{Attribute, Data, DataStruct, Generics, Ident, LitStr, Meta, Visibility};
use syn::spanned::Spanned as _;
use quote::quote;

use crate::common::{generate_field_impls, iter_bytes_attrs, parse_toplevel_input};


/***** PARSING FUNCTIONS *****/
/// Attempts to parse the toplevel attributes of the struct.
/// 
/// # Arguments
/// - `attrs`: The list of [`Attribute`]s to parse.
/// 
/// # Returns
/// A new [`ToplevelAttributes`] representing the parsed information.
/// 
/// # Errors
/// This function may error if any of the given attributes was ill-formed.
fn parse_toplevel_attrs(attrs: Vec<Attribute>) -> Result<ToplevelAttributes, Diagnostic> {
    let mut res: ToplevelAttributes = Default::default();
    iter_bytes_attrs(attrs, |arg: Meta| {
        match arg {
            Meta::NameValue(nv) => if nv.path.is_ident("input_name") {
                res.name = parse_toplevel_input(nv)?;
                Ok(())

            } else {
                return Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown toplevel `#[bytes(...)]` argument{}", if let Some(ident) = nv.path.get_ident() { format!(" '{ident}'") } else { String::new() })));
            },

            Meta::Path(p) => { return Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown toplevel `#[bytes(...)]` argument{}", if let Some(ident) = p.get_ident() { format!(" '{ident}'") } else { String::new() }))); },
            Meta::List(l) => { return Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown toplevel `#[bytes(...)]` argument{}", if let Some(ident) = l.path.get_ident() { format!(" '{ident}'") } else { String::new() }))); },
        }
    })?;
    Ok(res)
}





/***** HELPER STRUCTS *****/
/// Defines what we parsed from the toplevel attributes.
struct ToplevelAttributes {
    /// The name of the input argument.
    name : LitStr,
}
impl Default for ToplevelAttributes {
    fn default() -> Self {
        Self {
            name : LitStr::new("bytes", Span::call_site()),
        }
    }
}





/***** LIBRARY *****/
/// Takes the parsed struct and implements [`TryFromBytes`] for it.
/// 
/// # Arguments
/// - `ident`: The identifier of the parsed struct/enum/w/e.
/// - `data`: The contents of the parsed struct/enum/w/e.
/// - `attrs`: The list of attributes parsed from the main struct/enum/w/e.
/// - `generics`: The generics part of this struct/enum/w/e/.
/// - `vis`: The visibility markers for this struct/enum/w/e.
/// 
/// # Errors
/// This function may error if any of the attributes were ill-formed.
pub fn derive(ident: Ident, data: Data, attrs: Vec<Attribute>, generics: Generics, _vis: Visibility) -> Result<TokenStream, Diagnostic> {
    // Unwrap the Data as a struct
    let data: DataStruct = match data {
        Data::Struct(data) => data,
        Data::Enum(e)      => { return Err(Diagnostic::spanned(e.enum_token.span, Level::Error, "Cannot derive TryFromBytes on an enum".into())); }
        Data::Union(u)     => { return Err(Diagnostic::spanned(u.union_token.span, Level::Error, "Cannot derive TryFromBytes on a union".into())); }
    };

    // Parse the toplevel attributes first
    let top_attrs: ToplevelAttributes = parse_toplevel_attrs(attrs)?;

    // Generate the sub-parts of the implementation
    let input: Ident = Ident::new(&top_attrs.name.value(), top_attrs.name.span());
    let (parse_impl, self_impl, add_impl): (Vec<TokenStream2>, Vec<TokenStream2>, Vec<TokenStream2>) = generate_field_impls(&input, data)?;

    // Generate the contents of the impl
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();
    let try_from_bytes_impl: TokenStream2 = quote! {
        impl #impl_generics ::bytes::TryFromBytesDynamic<()> for #ident #type_generics #where_clause {
            type Error = ::bytes::errors::ParseError;

            #[automatically_derived]
            fn try_from_bytes_dynamic(_: (), #input: impl ::core::convert::AsRef<[::core::primitive::u8]>) -> ::std::result::Result<Self, Self::Error> {
                // Prepare parsing everything
                let #input: &[::core::primitive::u8] = #input.as_ref();
                let mut cumulative_offset: ::core::primitive::usize = 0;

                // Next, parse everything, but we parse to identifiers to allow other fields to access each other
                #(#parse_impl)*

                // Create ourselves
                ::std::result::Result::Ok(Self {
                    #(#self_impl)*
                })
            }
        }

        impl #impl_generics ::bytes::ParsedLength for #ident #type_generics #where_clause {
            #[automatically_derived]
            fn parsed_len(&self) -> ::core::primitive::usize {
                // Simply add all fields
                0 #(#add_impl)*
            }
        }
    };

    // OK, done
    Ok(try_from_bytes_impl.into())
}
