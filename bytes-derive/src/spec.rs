//  SPEC.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 14:12:16
//  Last edited:
//    09 Oct 2023, 16:49:39
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines traits and structs shared across the crate.
// 

use proc_macro2::Span;
use syn::{Expr, ExprStruct, Ident, Path, PathArguments, PathSegment, Type, TypePath};
use syn::punctuated::Punctuated;
use syn::token::{Brace, PathSep};


/***** LIBRARY *****/
/// Defines everything we need to know about generating a `TryFromBytesDynamic` impl.
#[derive(Clone)]
pub struct TryFromBytesDynamicInfo {
    /// Shared metadata with [`TryToBytesDynamicInfo`].
    pub metadata : MetadataInfo,
    /// The fields we processed.
    pub fields   : Vec<FieldParserInfo>,
}
impl TryFromBytesDynamicInfo {
    /// Generates default parser info.
    /// 
    /// # Arguments
    /// - `name`: The name of the type for which we're deriving.
    /// 
    /// # Returns
    /// A new instance of self that can be tweaked based on info we find in the struct def.
    #[inline]
    pub fn default(name: Ident) -> Self {
        Self {
            metadata : MetadataInfo::default_parser(name),
            fields   : vec![],
        }
    }
}



/// Defines everything we need to know about generating a `TryToBytesDynamic` impl.
#[derive(Clone)]
pub struct TryToBytesDynamicInfo {
    /// Shared metadata with [`TryFromBytesDynamicInfo`].
    pub metadata : MetadataInfo,
    /// The fields we processed.
    pub fields   : Vec<FieldSerializerInfo>,
}
impl TryToBytesDynamicInfo {
    // /// Generates default serializer info.
    // /// 
    // /// # Arguments
    // /// - `name`: The name of the type for which we're deriving.
    // /// 
    // /// # Returns
    // /// A new instance of self that can be tweaked based on info we find in the struct def.
    // #[inline]
    // pub fn default(name: Ident) -> Self {
    //     Self {
    //         metadata : MetadataInfo::default_serializer(name),
    //         fields   : vec![],
    //     }
    // }
}



/// Defines metadata shared across both the parser and serializer info's.
#[derive(Clone)]
pub struct MetadataInfo {
    /// The name of the type.
    pub name         : Ident,
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
    /// # Arguments
    /// - `name`: The name of the type for which we're deriving.
    /// 
    /// # Returns
    /// A new instance of Self with default settings.
    #[inline]
    pub fn default_parser(name: Ident) -> Self {
        // Build the default path segments
        let mut segments: Punctuated<PathSegment, PathSep> = Punctuated::default();
        segments.push(PathSegment {
            ident     : Ident::new("bytes", Span::call_site()),
            arguments : PathArguments::None,
        });
        segments.push(PathSegment {
            ident     : Ident::new("no_input", Span::call_site()),
            arguments : PathArguments::None,
        });
        segments.push(PathSegment {
            ident     : Ident::new("NoInput", Span::call_site()),
            arguments : PathArguments::None,
        });

        // OK, build self
        Self {
            name,
            input_name   : Ident::new("reader", Span::call_site()),
            dynamic_name : Ident::new("input", Span::call_site()),
            dynamic_ty   : (Type::Path(TypePath {
                qself : None,
                path  : Path {
                    leading_colon : Some(PathSep(Span::call_site())),
                    segments,
                },
            }), Span::call_site()),
        }
    }

    // /// Generates default metadata info for the serializer.
    // /// 
    // /// # Arguments
    // /// - `name`: The name of the type for which we're deriving.
    // /// 
    // /// # Returns
    // /// A new instance of Self with default settings.
    // #[inline]
    // pub fn default_serializer(name: Ident) -> Self {
    //     Self {
    //         name,
    //         input_name   : Ident::new("writer", Span::call_site()),
    //         dynamic_name : Ident::new("input", Span::call_site()),
    //         dynamic_ty   : (Type::Tuple(TypeTuple { paren_token: Paren(Span::call_site()), elems: Punctuated::default() }), Span::call_site()),
    //     }
    // }
}



/// Defines the field information we want to know for the parser.
#[derive(Clone)]
pub struct FieldParserInfo {
    /// The common part of the info
    pub common : FieldCommonInfo,
}
impl FieldParserInfo {
    /// Creates a default version of this info but with some context info.
    /// 
    /// # Arguments
    /// - `name`: The identifier naming this field.
    /// - `ty`: The type of the field. Given as a tuple of the type and a "real" source Span.
    /// 
    /// # Returns
    /// A new instance of self that has the default values for a parser field.
    #[inline]
    pub fn default(name: Ident, ty: (Type, Span)) -> Self {
        Self {
            common : FieldCommonInfo::default(name, ty),
        }
    }
}

/// Defines the field information we want to know for the serializer.
#[derive(Clone)]
pub struct FieldSerializerInfo {
    /// The common part of the info
    pub common : FieldCommonInfo,
}
impl FieldSerializerInfo {
    // /// Creates a default version of this info but with some context info.
    // /// 
    // /// # Arguments
    // /// - `name`: The identifier naming this field.
    // /// - `ty`: The type of the field. Given as a tuple of the type and a "real" source Span.
    // /// 
    // /// # Returns
    // /// A new instance of self that has the default values for a serializer field.
    // #[inline]
    // pub fn default(name: Ident, ty: (Type, Span)) -> Self {
    //     Self {
    //         common : FieldCommonInfo::default(name, ty),
    //     }
    // }
}

/// Defines the fields common to both the serializer and the parser.
#[derive(Clone)]
pub struct FieldCommonInfo {
    /// Whether to process this field at all.
    pub enabled : bool,

    /// The real name of this field.
    pub real_name : Ident,
    /// The name of this field for other dynamic input.
    pub dyn_name  : Ident,
    /// The real type of this field.
    pub real_ty   : Type,
    /// The type as which this field will be serialized/deserialized.
    pub parse_ty  : (Type, Span),

    /// Any dynamic input necessary.
    pub input : Expr,
}
impl FieldCommonInfo {
    /// Creates a default version of this info but with some context info.
    /// 
    /// # Arguments
    /// - `name`: The identifier naming this field.
    /// - `ty`: The type of the field. Given as a tuple of the type and a "real" source Span.
    /// 
    /// # Returns
    /// A new instance of self that has the default values common to all fields.
    #[inline]
    pub fn default(name: Ident, ty: (Type, Span)) -> Self {
        // Build the default path segments
        let mut segments: Punctuated<PathSegment, PathSep> = Punctuated::default();
        segments.push(PathSegment {
            ident     : Ident::new("bytes", Span::call_site()),
            arguments : PathArguments::None,
        });
        segments.push(PathSegment {
            ident     : Ident::new("no_input", Span::call_site()),
            arguments : PathArguments::None,
        });
        segments.push(PathSegment {
            ident     : Ident::new("NoInput", Span::call_site()),
            arguments : PathArguments::None,
        });

        // OK, build self
        Self {
            enabled : false,

            real_name : name.clone(),
            dyn_name  : name,
            real_ty   : ty.0.clone(),
            parse_ty  : ty,

            input : Expr::Struct(ExprStruct {
                attrs : vec![],
                qself : None,
                path  : Path {
                    leading_colon : Some(PathSep(Span::call_site())),
                    segments,
                },
                brace_token : Brace(Span::call_site()),
                fields      : Punctuated::default(),
                dot2_token  : None,
                rest        : None,
            }),
        }
    }
}
