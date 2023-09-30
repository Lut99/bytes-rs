//  PARSE.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 14:11:47
//  Last edited:
//    30 Sep 2023, 14:44:38
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines functions for parsing Rust's [`TokenStream`]s.
// 

use proc_macro_error::{Diagnostic, Level};
use syn::{parse_str, Attribute, DataStruct, Expr, ExprLit, Ident, Lit, LitStr, Meta, Path, Token};
use syn::parse::ParseBuffer;
use syn::spanned::Spanned as _;

use crate::spec::{MetadataInfo, TryFromBytesDynamicInfo};


/****** HELPERS *****/
/// Parses an attribute if it's `#[bytes(...)]` and calls a callback for every such attribute.
/// 
/// # Arguments
/// - `attr`: The [`Attribute`] to parse.
/// - `path_callback`: The function to call for every parsed nested attribute if `#[bytes]` is a path. If it errors, then the parser immediately propagates the result to its own error.
/// - `list_callback`: The function to call for every parsed nested attribute if `#[bytes(...)]` is a list. If it errors, then the parser immediately propagates the result to its own error.
/// 
/// # Errors
/// This function may error if we failed to parse the contents of `#[bytes(...)]` or if any callback errored.
fn parse_attr(attr: Attribute, mut path_callback: impl FnMut(Path) -> Result<(), Diagnostic>, mut list_callback: impl FnMut(Path, Meta) -> Result<(), Diagnostic>) -> Result<(), Diagnostic> {
    // Match the attribute's meta
    match attr.meta {
        Meta::Path(p) => if p.is_ident("bytes") { path_callback(p)?; },
        Meta::List(l) => if l.path.is_ident("bytes") {
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
                list_callback(arg)?;
            }
        },

        // Otherwise, ignored
        Meta::NameValue(_) => {},
    }

    // Alright that's it
    Ok(())
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
    
}





/****** LIBRARY *****/
/// Parses toplevel & field attributes for the [`TryFromBytesDynamic`] macro.
/// 
/// # Arguments
/// - `attrs`: The list of [`Attribute`]s that we will attempt to parse.
/// - `data`: The [`DataStruct`] that contains the fields we will parse field attributes from.
/// 
/// # Returns
/// A [`TryFromBytesDynamicInfo`] that carries the information we parse from the attributes.
/// 
/// # Errors
/// This function errors if we failed to parse attributes in the `#[bytes(...)]` attribute.
pub fn parse_parser(attrs: Vec<Attribute>, data: DataStruct) -> Result<TryFromBytesDynamicInfo, Diagnostic> {
    // Define the default settings to modify based on what attributes we read
    let mut info: TryFromBytesDynamicInfo = Default::default();

    // First, go through all the toplevel attributes
    for attr in attrs {
        // Parse them as toplevel attributes
        parse_attr(attr, |ident: Path| -> Result<(), Diagnostic> {
            Err(Diagnostic::spanned(ident.span(), Level::Error, "Toplevel `#[bytes]` must have arguments".into()).span_suggestion(ident.span(), "#[bytes(...)]", "Try this".into()))
        }, |bytes_ident: Path, meta: Meta| -> Result<(), Diagnostic> {
            // Further match the meta
            match meta {
                Meta::NameValue(nv) => if nv.path.is_ident("input_name") {
                    // Parse the value as a string literal
                    if let Expr::Lit(ExprLit { lit: Lit::Str(lit), .. }) = nv.value {
                        // Store the value as an identifier
                        info.metadata.input_name = Ident::new(&lit.value(), lit.span());
                        Ok(())

                    } else {
                        Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Expected string literal{}", if let Some(text) = nv.path.span().source_text() { format!(", not '{text}'") } else { String::new() })))
                    }

                } else if nv.path.is_ident("dynamic_name") {
                    // Parse the value as a string literal
                    if let Expr::Lit(ExprLit { lit: Lit::Str(lit), .. }) = nv.value {
                        // Store the value as an identifier
                        info.metadata.dynamic_name = Ident::new(&lit.value(), lit.span());
                        Ok(())

                    } else {
                        Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Expected string literal{}", if let Some(text) = nv.path.span().source_text() { format!(", not '{text}'") } else { String::new() })))
                    }

                } else if nv.path.is_ident("dynamic_ty") {
                    // Parse the value as a string literal
                    if let Expr::Lit(ExprLit { lit: Lit::Str(lit), .. }) = nv.value {
                        // Parse as a type identifier
                        match parse_str(&lit.value()) {
                            Ok(ty)   => { info.metadata.dynamic_name = ty; Ok(()) },
                            Err(err) => Err(Diagnostic::spanned(lit.span(), Level::Error, "Failed to parse string literal as a Rust type".into()).span_error(lit.span(), err.to_string())),
                        }

                    } else {
                        Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Expected string literal{}", if let Some(text) = nv.path.span().source_text() { format!(", not '{text}'") } else { String::new() })))
                    }

                } else {
                    Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` key/value attribute{}", if let Some(text) = nv.path.span().source_text() { format!(" '{text}'") } else { String::new() })))
                },

                // Ignored otherwise
                Meta::Path(p) => Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown `#[bytes(...)]` attribute{}", if let Some(text) = p.span().source_text() { format!(" '{text}'") } else { String::new() }))),
                Meta::List(l) => Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown `#[bytes(...)]` list attribute{}", if let Some(text) = l.path.span().source_text() { format!(" '{text}'") } else { String::new() }))),
            }
        })?;
    }

    // Alright done!
    Ok(info)
}
