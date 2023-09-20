//  TRY FROM BYTES.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:09:49
//  Last edited:
//    20 Sep 2023, 10:36:02
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the derivation procedure for the [`TryFromBytes`].
// 

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use proc_macro_error::{Diagnostic, Level};
use syn::{Attribute, Data, DataStruct, Expr, ExprLit, Generics, Ident, Lit, LitInt, Meta, Token, Type, Visibility};
use syn::parse::ParseBuffer;
use syn::spanned::Spanned as _;
use quote::quote;


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
    let res: ToplevelAttributes = Default::default();
    for attr in attrs {
        // Match on the kind of attribute found
        match attr.meta {
            Meta::Path(_)      |
            Meta::NameValue(_) |
            Meta::List(_)      => { continue; },
        }
    }
    Ok(res)
}

/// Attempts to parse the fieldlevel attributes of the struct.
/// 
/// # Arguments
/// - `attrs`: The list of [`Attribute`]s to parse.
/// 
/// # Returns
/// A new [`FieldAttributes`] representing the parsed information, or [`None`] if none of our attributes were present.
/// 
/// # Errors
/// This function may error if any of the given attributes was ill-formed.
fn parse_field_attrs(attrs: Vec<Attribute>) -> Result<Option<FieldAttributes>, Diagnostic> {
    let mut found: bool = false;
    let mut res: FieldAttributes = Default::default();
    for attr in attrs {
        // Match on the kind of attribute found
        match attr.meta {
            // Match our own attribute
            Meta::List(l) => if l.path.is_ident("bytes") {
                // Parse the list of things given to it
                let args: Vec<Meta> = match l.parse_args_with(|buffer: &ParseBuffer| {
                    // Repeatedly parsed metas separated by commands
                    let mut metas: Vec<Meta> = vec![ buffer.parse()? ];
                    while !buffer.is_empty() {
                        // Parse a comma then a meta
                        buffer.parse::<Token!(,)>()?;
                        metas.push(buffer.parse()?);
                    }
                    Ok(metas)
                }) {
                    Ok(args) => args,
                    Err(err) => { return Err(Diagnostic::spanned(l.tokens.span(), Level::Error, "Failed to parse `#[bytes(...)]` arguments".into()).span_error(err.span(), err.to_string())); },
                };

                // Iterate over them
                for arg in args {
                    match arg {
                        Meta::NameValue(nv) => if nv.path.is_ident("dynamic") {
                            // We simply take the expression as-is
                            res.dynamic = Some(nv.value);

                        } else if nv.path.is_ident("offset") {
                            // Parse it as a number literal of some sorts
                            let value_span: Span = nv.value.span();
                            if let Expr::Lit(ExprLit { attrs: _, lit: Lit::Int(lit) }) = nv.value {
                                res.offset = Some(lit);
                            } else {
                                return Err(Diagnostic::spanned(value_span, Level::Error, "Expected integer literal".into()));
                            }

                        } else if nv.path.is_ident("len") || nv.path.is_ident("length") {
                            // Parse it as a number literal of some sorts
                            let value_span: Span = nv.value.span();
                            if let Expr::Lit(ExprLit { attrs: _, lit: Lit::Int(lit) }) = nv.value {
                                res.length = Some(lit);
                            } else {
                                return Err(Diagnostic::spanned(value_span, Level::Error, "Expected integer literal".into()));
                            }

                        } else {
                            return Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` argument{}", if let Some(ident) = nv.path.get_ident() { format!(" '{ident}'") } else { String::new() })));
                        },

                        // The rest we never match
                        Meta::Path(p) => {
                            return Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown `#[bytes(...)]` argument{}", if let Some(ident) = p.get_ident() { format!(" '{ident}'") } else { String::new() })));
                        },
                        Meta::List(l) => {
                            return Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` argument{}", if let Some(ident) = l.path.get_ident() { format!(" '{ident}'") } else { String::new() })));
                        },
                    }
                }

                // Regardless of what we parsed, the presence of the main `#[bytes(...)]` indicates this field should be parsed.
                found = true;
            } else {
                continue;
            },

            // Match single-path things
            Meta::Path(p) => if p.is_ident("bytes") {
                // This tells us nothing except this field should be parsed with default options
                found = true;
            } else {
                continue;
            },

            // The rest is not our thing
            Meta::NameValue(_) => { continue; },
        }
    }

    // Return the results - if we are told to parse this field, that is
    if found {
        Ok(Some(res))
    } else {
        Ok(None)
    }
}





/***** HELPER STRUCTS *****/
/// Defines what we parsed from the toplevel attributes.
struct ToplevelAttributes {
    
}
impl Default for ToplevelAttributes {
    fn default() -> Self {
        Self {
            
        }
    }
}

/// Defines what we parsed from the field-level attributes.
struct FieldAttributes {
    /// Whether this attribute is dynamic and, if so, which value needs to be passed to it.
    dynamic : Option<Expr>,
    /// Any explicit offset that is given.
    offset  : Option<LitInt>,
    /// Any explicit length that is given.
    length  : Option<LitInt>,
}
impl Default for FieldAttributes {
    fn default() -> Self {
        Self {
            dynamic : None,
            offset  : None,
            length  : None,
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

    // Next, iterate over all fields to parse those attributes
    let mut field_attrs: Vec<Option<FieldAttributes>> = Vec::with_capacity(data.fields.len());
    for (i, field) in data.fields.into_iter().enumerate() {
        // Parse the identifier of the field
        let ident: Ident = if let Some(field) = field.ident { field } else { Ident::new(&i.to_string(), field.span()) };
        // Parse the type of the identifier
        let ty: Type = field.ty;

        field_attrs.push(parse_field_attrs(field.attrs)?);
    }

    // Generate the populates of the Self
    let self_pop: Vec<TokenStream2> = Vec::with_capacity(field_attrs.len());
    for field in field_attrs {
        if let Some(field) = field {
            // Generate the parser

        } else {
            // Generate a `Default::default()` instead

        }
    }

    // Generate the contents of the impl
    let code: TokenStream2 = quote! {
        impl ::bytes::TryFromBytes for #ident {
            type Error = ::bytes::errors::ParseError;

            fn try_from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
                
            }
        }
    };

    // OK, done
    Ok(quote!{}.into())
}
