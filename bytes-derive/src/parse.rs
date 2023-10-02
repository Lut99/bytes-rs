//  PARSE.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 14:11:47
//  Last edited:
//    02 Oct 2023, 20:58:55
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines functions for parsing Rust's [`TokenStream`]s.
// 

use proc_macro2::Span;
use proc_macro_error::{Diagnostic, Level};
use syn::{parse_str, Attribute, DataStruct, Expr, ExprLit, Ident, Lit, LitBool, LitStr, Meta, Path, Token, Type};
use syn::parse::ParseBuffer;
use syn::spanned::Spanned as _;

use crate::spec::{FieldParserInfo, FieldSerializerInfo, TryFromBytesDynamicInfo, TryToBytesDynamicInfo};


/****** HELPERS *****/
/// Parses an attribute if it's `#[bytes(...)]` and calls a callback for every such attribute.
/// 
/// # Arguments
/// - `attr`: The [`Attribute`] to parse.
/// - `path_callback`: The function to call for every parsed nested attribute if `#[bytes]` is a path. If it errors, then the parser immediately propagates the result to its own error.
/// - `list_callback`: The function to call for every parsed nested attribute if `#[bytes(...)]` is a list. If it errors, then the parser immediately propagates the result to its own error.
/// 
/// # Returns
/// Whether any `#[bytes(...)]`-attribute was found
/// 
/// # Errors
/// This function may error if we failed to parse the contents of `#[bytes(...)]` or if any callback errored.
fn parse_attr(attr: Attribute, mut path_callback: impl FnMut(Path) -> Result<(), Diagnostic>, mut list_callback: impl FnMut(&Path, Meta) -> Result<(), Diagnostic>) -> Result<bool, Diagnostic> {
    // Match the attribute's meta
    let mut found: bool = false;
    match attr.meta {
        Meta::Path(p) => if p.is_ident("bytes") { found = true; path_callback(p)?; },
        Meta::List(l) => if l.path.is_ident("bytes") {
            found = true;

            // Attempt to parse the list of attribues
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

            // Call the callback for every of those
            for arg in args {
                list_callback(&l.path, arg)?;
            }
        },

        // Otherwise, ignored
        Meta::NameValue(_) => {},
    }

    // Alright that's it
    Ok(found)
}

/// Parses an [`Expr`] as a boolean literal.
/// 
/// # Arguments
/// - `expr`: The [`Expr`] to parse.
/// 
/// # Returns
/// The integer literal as a [`LitBool`].
/// 
/// # Errors
/// This function may error if the expression is something else than a boolean literal.
fn parse_expr_as_bool_lit(expr: Expr) -> Result<LitBool, Diagnostic> {
    if let Expr::Lit(ExprLit { lit: Lit::Bool(lit), .. }) = expr {
        Ok(lit)
    } else {
        Err(Diagnostic::spanned(expr.span(), Level::Error, format!("Expected boolean literal{}", if let Some(text) = expr.span().source_text() { format!(", got '{text}'") } else { String::new() })))
    }
}

/// Parses an [`Expr`] as a string literal.
/// 
/// # Arguments
/// - `expr`: The [`Expr`] to parse.
/// 
/// # Returns
/// The string literal as a [`LitStr`].
/// 
/// # Errors
/// This function may error if the expression is something else than a string literal.
fn parse_expr_as_str_lit(expr: Expr) -> Result<LitStr, Diagnostic> {
    if let Expr::Lit(ExprLit { lit: Lit::Str(lit), .. }) = expr {
        Ok(lit)
    } else {
        Err(Diagnostic::spanned(expr.span(), Level::Error, format!("Expected string literal{}", if let Some(text) = expr.span().source_text() { format!(", got '{text}'") } else { String::new() })))
    }
}

/// Parses an [`Expr`] as a string literal, and then parses the string literal's contents as a [`Type`].
/// 
/// # Arguments
/// - `expr`: The [`Expr`] to parse.
/// 
/// # Returns
/// The type as a [`Type`], combined with a [`Span`] that actually represents where the user wrote the type.
/// 
/// # Errors
/// This function may error if the expression is something else than a string literal denoting a Rust type.
fn parse_expr_as_str_lit_type(expr: Expr) -> Result<(Type, Span), Diagnostic> {
    // Parse the value as a string literal
    let expr_span: Span = expr.span();
    let lit: LitStr = parse_expr_as_str_lit(expr)?;
                    
    // Parse as a type identifier
    match parse_str(&lit.value()) {
        Ok(ty)   => Ok((ty, expr_span)),
        Err(err) => Err(Diagnostic::spanned(lit.span(), Level::Error, "Failed to parse string literal as a Rust type".into()).span_error(lit.span(), err.to_string())),
    }
}





/****** LIBRARY *****/
/// Parses toplevel & field attributes for the [`TryFromBytesDynamic`] macro.
/// 
/// # Arguments
/// - `attrs`: The list of [`Attribute`]s that we will attempt to parse.
/// - `name`: The name of the struct we're parsing.
/// - `data`: The [`DataStruct`] that contains the fields we will parse field attributes from.
/// - `allow_dynamic`: Whether to allow dynamic input to the main struct.
/// 
/// # Returns
/// A [`TryFromBytesDynamicInfo`] that carries the information we parse from the attributes.
/// 
/// # Errors
/// This function errors if we failed to parse attributes in the `#[bytes(...)]` attribute.
pub fn parse_parser(attrs: Vec<Attribute>, name: Ident, data: DataStruct, allow_dynamic: bool) -> Result<TryFromBytesDynamicInfo, Diagnostic> {
    // Define the default settings to modify based on what attributes we read
    let mut info: TryFromBytesDynamicInfo = TryFromBytesDynamicInfo::default(name);

    // First, go through all the toplevel attributes
    for attr in attrs {
        // Parse them as toplevel attributes
        parse_attr(attr, |ident: Path| -> Result<(), Diagnostic> {
            Err(Diagnostic::spanned(ident.span(), Level::Error, "Toplevel `#[bytes]` must have arguments".into()).span_suggestion(ident.span(), "#[bytes(...)]", "Try this".into()))
        }, |_: &Path, meta: Meta| -> Result<(), Diagnostic> {
            // Further match the meta
            match meta {
                Meta::NameValue(nv) => if nv.path.is_ident("input_name") {
                    // Store the value as an identifier
                    let lit: LitStr = parse_expr_as_str_lit(nv.value)?;
                    info.metadata.input_name = Ident::new(&lit.value(), lit.span());
                    Ok(())

                } else if allow_dynamic && nv.path.is_ident("dynamic_name") {
                    // Store the value as an identifier
                    let lit: LitStr = parse_expr_as_str_lit(nv.value)?;
                    info.metadata.dynamic_name = Ident::new(&lit.value(), lit.span());
                    Ok(())

                } else if allow_dynamic && nv.path.is_ident("dynamic_ty") {
                    // Store the value as a type
                    info.metadata.dynamic_ty = parse_expr_as_str_lit_type(nv.value)?;
                    Ok(())

                } else {
                    Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` key/value attribute{}", if let Some(text) = nv.path.span().source_text() { format!(" '{text}'") } else { String::new() })))
                },

                // Ignored otherwise
                Meta::Path(p) => Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown `#[bytes(...)]` attribute{}", if let Some(text) = p.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                Meta::List(l) => Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` list attribute{}", if let Some(text) = l.path.span().source_text() { format!(" '{text}'") } else { String::new() }))),
            }
        })?;
    }

    // Next, go through all the fields and do the same there again
    info.fields.reserve(data.fields.len());
    for (i, field) in data.fields.into_iter().enumerate() {
        let ty_span: Span = field.ty.span();
        let mut field_info: FieldParserInfo = FieldParserInfo::default(field.ident.unwrap_or_else(|| Ident::new(&format!("{i}"), Span::call_site())), (field.ty, ty_span));
        for attr in field.attrs {
            // Parse them as toplevel attributes
            field_info.common.enabled = parse_attr(attr, |_: Path| -> Result<(), Diagnostic> {
                // We can safely ignore
                Ok(())
            }, |_: &Path, meta: Meta| -> Result<(), Diagnostic> {
                // Further match the meta
                match meta {
                    Meta::NameValue(nv) => if nv.path.is_ident("enabled") {
                        // Store the value as an identifier
                        let lit: LitBool = parse_expr_as_bool_lit(nv.value)?;
                        field_info.common.enabled = lit.value();
                        Ok(())

                    } else if nv.path.is_ident("name") {
                        // Store the value as an identifier
                        let lit: LitStr = parse_expr_as_str_lit(nv.value)?;
                        field_info.common.dyn_name = Ident::new(&lit.value(), lit.span());
                        Ok(())

                    } else if nv.path.is_ident("as") {
                        // Store the value as a type
                        field_info.common.parse_ty = parse_expr_as_str_lit_type(nv.value)?;
                        Ok(())

                    } else if nv.path.is_ident("offset") {
                        // Store the value as the arbitrary expression we got
                        field_info.common.offset = Some(nv.value);
                        Ok(())

                    } else if nv.path.is_ident("input") {
                        // Store the value as the arbitrary expression we got
                        field_info.common.input = nv.value;
                        Ok(())

                    } else {
                        Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` key/value attribute{}", if let Some(text) = nv.path.span().source_text() { format!(" '{text}'") } else { String::new() })))
                    },

                    // We could recurse here by observing that something is only applicable for parsers/serializers
                    Meta::List(l) => if l.path.is_ident("from") || l.path.is_ident("parse") || l.path.is_ident("parser") {
                        parse_attr(attr, |_: Path| -> Result<(), Diagnostic> {
                            // We can safely ignore
                            Ok(())
                        }, |_: &Path, meta: Meta| -> Result<(), Diagnostic> {
                            // Further match the meta
                            match meta {
                                Meta::NameValue(nv) => if nv.path.is_ident("enabled") {
                                    // Store the value as an identifier
                                    let lit: LitBool = parse_expr_as_bool_lit(nv.value)?;
                                    field_info.common.enabled = lit.value();
                                    Ok(())
            
                                } else if nv.path.is_ident("name") {
                                    // Store the value as an identifier
                                    let lit: LitStr = parse_expr_as_str_lit(nv.value)?;
                                    field_info.common.dyn_name = Ident::new(&lit.value(), lit.span());
                                    Ok(())
            
                                } else if nv.path.is_ident("as") {
                                    // Store the value as a type
                                    field_info.common.parse_ty = parse_expr_as_str_lit_type(nv.value)?;
                                    Ok(())
            
                                } else if nv.path.is_ident("offset") {
                                    // Store the value as the arbitrary expression we got
                                    field_info.common.offset = Some(nv.value);
                                    Ok(())
            
                                } else if nv.path.is_ident("input") {
                                    // Store the value as the arbitrary expression we got
                                    field_info.common.input = nv.value;
                                    Ok(())
            
                                } else {
                                    Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown `#[bytes({}(...))]` key/value attribute{}", l.path.span().source_text().unwrap(), if let Some(text) = nv.path.span().source_text() { format!(" '{text}'") } else { String::new() })))
                                },

                                // The rest is never allowed
                                Meta::Path(p) => Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown `#[bytes({}(...))]` attribute{}", l.path.span().source_text().unwrap(), if let Some(text) = p.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                                Meta::List(l) => Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown `#[bytes({}(...))]` list attribute{}", l.path.span().source_text().unwrap(), if let Some(text) = l.path.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                            }
                        });
                        Ok(())

                    } else {
                        Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` list attribute{}", if let Some(text) = l.path.span().source_text() { format!(" '{text}'") } else { String::new() })))
                    },

                    // Ignored otherwise
                    Meta::Path(p) => Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown `#[bytes(...)]` attribute{}", if let Some(text) = p.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                }
            })?;
        }

        // Add the info
        info.fields.push(field_info);
    }

    // Alright done!
    Ok(info)
}



/// Parses toplevel & field attributes for the [`TryToBytesDynamic`] macro.
/// 
/// # Arguments
/// - `attrs`: The list of [`Attribute`]s that we will attempt to parse.
/// - `name`: The name of the struct we're parsing.
/// - `data`: The [`DataStruct`] that contains the fields we will parse field attributes from.
/// - `allow_dynamic`: Whether to allow dynamic input to the main struct.
/// 
/// # Returns
/// A [`TryToBytesDynamicInfo`] that carries the information we parse from the attributes.
/// 
/// # Errors
/// This function errors if we failed to parse attributes in the `#[bytes(...)]` attribute.
#[inline]
pub fn parse_serializer(attrs: Vec<Attribute>, name: Ident, data: DataStruct, allow_dynamic: bool) -> Result<TryToBytesDynamicInfo, Diagnostic> {
    // For now, it's actually exactly the same xZ
    let info: TryFromBytesDynamicInfo = parse_parser(attrs, name, data, allow_dynamic)?;
    Ok(TryToBytesDynamicInfo {
        metadata : info.metadata,
        fields   : info.fields.into_iter().map(|f| FieldSerializerInfo { common: f.common }).collect(),
    })
}
