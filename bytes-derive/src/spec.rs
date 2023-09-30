//  SPEC.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 14:12:16
//  Last edited:
//    30 Sep 2023, 16:48:26
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines traits and structs shared across the crate.
// 

use proc_macro2::Span;
use syn::{Ident, Type, TypeTuple};
use syn::punctuated::Punctuated;
use syn::token::Paren;


/***** LIBRARY *****/
/// Defines everything we need to know about generating a `TryFromBytesDynamic` impl.
#[derive(Clone)]
pub struct TryFromBytesDynamicInfo {
    /// Shared metadata with [`TryToBytesDynamicInfo`].
    pub metadata : MetadataInfo,
}
impl Default for TryFromBytesDynamicInfo {
    #[inline]
    fn default() -> Self {
        Self {
            metadata : MetadataInfo::default_parser(),
        }
    }
}



/// Defines everything we need to know about generating a `TryToBytesDynamic` impl.
#[derive(Clone)]
pub struct TryToBytesDynamicInfo {
    /// Shared metadata with [`TryFromBytesDynamicInfo`].
    pub metadata : MetadataInfo,
}
impl Default for TryToBytesDynamicInfo {
    #[inline]
    fn default() -> Self {
        Self {
            metadata : MetadataInfo::default_serializer(),
        }
    }
}



/// Defines metadata shared across both the parser and serializer info's.
#[derive(Clone)]
pub struct MetadataInfo {
    /// The name of the `reader`/`writer`-variable.
    pub input_name   : Ident,
    /// The name of the dynamic input.
    pub dynamic_name : Ident,
    /// The type of the dynamic input, together with its "actual" Span.
    pub dynamic_ty   : (Type, Span),
}
impl MetadataInfo {
    /// Generates default metadata info for the parser.
    /// 
    /// # Returns
    /// A new instance of Self with default settings.
    #[inline]
    pub fn default_parser() -> Self {
        Self {
            input_name   : Ident::new("reader", Span::call_site()),
            dynamic_name : Ident::new("input", Span::call_site()),
            dynamic_ty   : (Type::Tuple(TypeTuple { paren_token: Paren(Span::call_site()), elems: Punctuated::default() }), Span::call_site()),
        }
    }

    /// Generates default metadata info for the serializer.
    /// 
    /// # Returns
    /// A new instance of Self with default settings.
    #[inline]
    pub fn default_serializer() -> Self {
        Self {
            input_name   : Ident::new("writer", Span::call_site()),
            dynamic_name : Ident::new("input", Span::call_site()),
            dynamic_ty   : (Type::Tuple(TypeTuple { paren_token: Paren(Span::call_site()), elems: Punctuated::default() }), Span::call_site()),
        }
    }
}
