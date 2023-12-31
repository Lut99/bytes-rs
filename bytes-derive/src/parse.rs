//  PARSE.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 14:11:47
//  Last edited:
//    11 Oct 2023, 22:29:07
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines functions for parsing Rust's [`TokenStream`]s.
// 

use proc_macro2::Span;
use proc_macro_error::{Diagnostic, Level};
use syn::{parse_str, Attribute, DataStruct, Expr, ExprLit, Ident, Lit, LitBool, LitStr, Meta, MetaList, Path, Token, Type};
use syn::parse::ParseBuffer;
use syn::spanned::Spanned as _;

use crate::spec::{FieldParserInfo, FieldSerializerInfo, TryFromBytesDynamicInfo, TryToBytesDynamicInfo};


/****** HELPERS *****/
/// Parses the attributes in a [`Meta::List`].
/// 
/// # Arguments
/// - `tokens`: The [`MetaList`] encoding the tokens to parse.
/// 
/// # Returns
/// A new list of [`Meta`]s to further consider.
/// 
/// # Errors
/// This function may error if the given stream was not valid tokens.
fn parse_list_attrs(l: &MetaList) -> Result<Vec<Meta>, Diagnostic> {
    match l.parse_args_with(|buffer: &ParseBuffer| {
        // Repeatedly parsed metas separated by commands
        let mut metas: Vec<Meta> = vec![ buffer.parse()? ];
        while !buffer.is_empty() {
            // Parse a comma then a meta
            buffer.parse::<Token!(,)>()?;
            metas.push(buffer.parse()?);
        }
        Ok(metas)
    }) {
        Ok(args) => Ok(args),
        Err(err) => Err(Diagnostic::spanned(l.tokens.span(), Level::Error, "Failed to parse `#[bytes(...)]` arguments".into()).span_error(err.span(), err.to_string())),
    }
}

/// Parses an attribute if it's `#[bytes(...)]` and calls a callback for every such attribute.
/// 
/// # Arguments
/// - `is_parser`: Whether this is called for the parser (true) or the serializer (false).
/// - `attr`: The [`Attribute`] to parse.
/// - `callback`: The function to call for every parsed nested attribute. The Meta is only given if `#[bytes]` is accompanied with a list. The return value determines if the enableness needs to be overriden and if so, with what. If it errors, then the parser immediately propagates the result to its own error.
/// 
/// # Returns
/// Whether the parsed field should be enabled.
/// 
/// # Errors
/// This function may error if we failed to parse the contents of `#[bytes(...)]` or if any callback errored.
fn parse_attr(is_parser: bool, attr: Attribute, mut callback: impl FnMut(&Path, Option<Meta>) -> Result<Option<bool>, Diagnostic>) -> Result<bool, Diagnostic> {
    // Match the attribute's meta
    let mut found: bool = false;
    match attr.meta {
        Meta::Path(p) => if p.is_ident("bytes") { found = callback(&p, None)?.unwrap_or(true); },
        Meta::List(l) => if l.path.is_ident("bytes") {
            found = true;

            // Attempt to parse the list of attribues
            let args: Vec<Meta> = parse_list_attrs(&l)?;

            // Call the callback for every of those
            for arg in args {
                // Catch scoping meta's, i.e., `#[bytes(to(...))]` and such
                let is_parse_scoped: bool = arg.path().is_ident("from") || arg.path().is_ident("parse") || arg.path().is_ident("parser");
                let is_serialize_scoped: bool = arg.path().is_ident("to") || arg.path().is_ident("serialize") || arg.path().is_ident("serializer");
                if matches!(arg, Meta::List(_)) && (is_parse_scoped || is_serialize_scoped) {
                    let l: MetaList = if let Meta::List(l) = arg { l } else { unreachable!(); };

                    // Now only call the callback if the parser makes sense
                    if is_parser && is_parse_scoped || !is_parser && is_serialize_scoped {
                        // Recursively parse the meta
                        let args: Vec<Meta> = parse_list_attrs(&l)?;
                        for arg in args {
                            if let Some(new_found) = callback(&l.path, Some(arg))? {
                                found = new_found;
                            }
                        }
                    }
                } else {
                    // Otherwise, just call normally
                    if let Some(new_found) = callback(&l.path, Some(arg))? {
                        found = new_found;
                    }
                }
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

/// Parses a [`TryFromBytesDynamicInfo`] such that both the parse- and serialize macros have a use of it.
/// 
/// # Arguments
/// - `is_parser`: Whether we're doing this for the parser (true) or the serializer (false).
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
fn parse_try_from_bytes_dynamic(is_parser: bool, attrs: Vec<Attribute>, name: Ident, data: DataStruct, allow_dynamic: bool) -> Result<TryFromBytesDynamicInfo, Diagnostic> {
    // Define the default settings to modify based on what attributes we read
    let mut info: TryFromBytesDynamicInfo = TryFromBytesDynamicInfo::default(name);

    // First, go through all the toplevel attributes
    for attr in attrs {
        // Parse them as toplevel attributes
        parse_attr(is_parser, attr, |ident: &Path, meta: Option<Meta>| -> Result<Option<bool>, Diagnostic> {
            // Further match the meta
            match meta {
                Some(Meta::NameValue(nv)) => if nv.path.is_ident("input_name") {
                    // Store the value as an identifier
                    let lit: LitStr = parse_expr_as_str_lit(nv.value)?;
                    info.metadata.input_name = Ident::new(&lit.value(), lit.span());
                    Ok(None)

                } else if allow_dynamic && nv.path.is_ident("dynamic_name") {
                    // Store the value as an identifier
                    let lit: LitStr = parse_expr_as_str_lit(nv.value)?;
                    info.metadata.dynamic_name = Ident::new(&lit.value(), lit.span());
                    Ok(None)

                } else if allow_dynamic && nv.path.is_ident("dynamic_ty") {
                    // Store the value as a type
                    info.metadata.dynamic_ty = parse_expr_as_str_lit_type(nv.value)?;
                    Ok(None)

                } else if nv.path.is_ident("generate_refs") {
                    // Parse the value as a boolean literal
                    info.metadata.generate_refs = parse_expr_as_bool_lit(nv.value)?.value;
                    Ok(None)

                } else {
                    Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` key/value attribute{}", if let Some(text) = nv.path.span().source_text() { format!(" '{text}'") } else { String::new() })))
                },

                // If `None`, then a plain `#[bytes]` is given without list
                None => {
                    Err(Diagnostic::spanned(ident.span(), Level::Error, "Toplevel `#[bytes]` must have arguments".into()).span_suggestion(ident.span(), "#[bytes(...)]", "Try this".into()))
                },

                // Ignored otherwise
                Some(Meta::Path(p)) => Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown `#[bytes(...)]` attribute{}", if let Some(text) = p.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                Some(Meta::List(l)) => Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` list attribute{}", if let Some(text) = l.path.span().source_text() { format!(" '{text}'") } else { String::new() }))),
            }
        })?;
    }

    // Next, go through all the fields and do the same there again
    info.fields.reserve(data.fields.len());
    for (i, field) in data.fields.into_iter().enumerate() {
        let mut field_info: FieldParserInfo = FieldParserInfo::default(field.ident.unwrap_or_else(|| Ident::new(&format!("{i}"), Span::call_site())), field.ty);
        for attr in field.attrs {
            // Parse them as toplevel attributes
            field_info.common.enabled = parse_attr(is_parser, attr, |_: &Path, meta: Option<Meta>| -> Result<Option<bool>, Diagnostic> {
                // Further match the meta
                match meta.clone() {
                    Some(Meta::NameValue(nv)) => if nv.path.is_ident("enabled") {
                        // Store the value as an identifier
                        let lit: LitBool = parse_expr_as_bool_lit(nv.value)?;
                        Ok(Some(lit.value()))

                    } else if nv.path.is_ident("name") {
                        // Store the value as an identifier
                        let lit: LitStr = parse_expr_as_str_lit(nv.value)?;
                        field_info.common.dyn_name = Ident::new(&lit.value(), lit.span());
                        Ok(None)

                    } else if nv.path.is_ident("as_ty") {
                        // Store the value as a type
                        field_info.common.as_ty = Some(parse_expr_as_str_lit_type(nv.value)?);
                        Ok(None)

                    } else if nv.path.is_ident("try_as_ty") {
                        // Store the value as a type
                        field_info.common.try_as_ty = Some(parse_expr_as_str_lit_type(nv.value)?);
                        Ok(None)

                    // } else if nv.path.is_ident("offset") {
                    //     // Store the value as the arbitrary expression we got
                    //     field_info.common.offset = Some(nv.value);
                    //     Ok(())

                    } else if nv.path.is_ident("input") {
                        // Store the value as the arbitrary expression we got
                        field_info.common.input = nv.value;
                        Ok(None)

                    } else {
                        Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` key/value attribute{}", if let Some(text) = nv.path.span().source_text() { format!(" '{text}'") } else { String::new() })))
                    },

                    // If None, then means only `#[bytes]` is given
                    None => Ok(None),

                    // Ignored otherwise
                    Some(Meta::List(l)) => Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` list attribute{}", if let Some(text) = l.path.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                    Some(Meta::Path(p)) => Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown `#[bytes(...)]` attribute{}", if let Some(text) = p.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                }
            })?;
        }

        // Assert conflicting fields are not given both
        if let (Some((_, span1)), Some((_, span2))) = (&field_info.common.as_ty, &field_info.common.try_as_ty) {
            return Err(
                Diagnostic::new(Level::Error, "Cannot give both `as_ty` and `try_as_ty` attributes (choose one)".into())
                    .span_note(*span1, "`as_ty` given here".into())
                    .span_note(*span2, "`try_as_ty` given here".into())
            );
        }

        // Add the info
        info.fields.push(field_info);
    }

    // Alright done!
    Ok(info)
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
#[inline]
pub fn parse_parser(attrs: Vec<Attribute>, name: Ident, data: DataStruct, allow_dynamic: bool) -> Result<TryFromBytesDynamicInfo, Diagnostic> {
    parse_try_from_bytes_dynamic(true, attrs, name, data, allow_dynamic)
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
    let info: TryFromBytesDynamicInfo = parse_try_from_bytes_dynamic(false, attrs, name, data, allow_dynamic)?;
    Ok(TryToBytesDynamicInfo {
        metadata : info.metadata,
        fields   : info.fields.into_iter().map(|f| FieldSerializerInfo { common: f.common }).collect(),
    })
}
