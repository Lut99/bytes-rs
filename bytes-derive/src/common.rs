//  COMMON.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 17:39:26
//  Last edited:
//    21 Sep 2023, 13:44:20
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines common code between the two different derivations.
// 

use proc_macro2::{Span, TokenStream as TokenStream2};
use proc_macro_error::{Diagnostic, Level};
use syn::{Attribute, DataStruct, Expr, ExprLit, Ident, Meta, MetaNameValue, Lit, LitInt, LitStr, Token, Type};
use syn::parse::ParseBuffer;
use syn::spanned::Spanned as _;
use quote::{quote, quote_spanned};


/***** LIBRARY STRUCTS *****/
/// Defines what we want to know about each field.
pub struct Field {
    /// The identifier of the field.
    pub ident : Ident,
    /// The type of the field
    pub ty    : Type,
    /// The parsed attributes
    pub attrs : Option<FieldAttributes>,
}

/// Defines what we parsed from the field-level attributes.
pub struct FieldAttributes {
    /// Whether this attribute is dynamic and, if so, which value needs to be passed to it.
    pub dynamic : Option<Expr>,
    /// Any explicit offset that is given.
    pub offset  : Option<LitInt>,
    /// Any explicit length that is given.
    pub length  : Option<LitInt>,
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





/***** LIBRARY FUNCTIONS *****/
/// Defines a convenient iterator over elements in the list of the `#[bytes(...)]`-attribute.
/// 
/// # Arguments
/// - `attrs`: The attributes to iterate over.
/// - `callback`: The [`FnMut`] to call for every attribute found.
/// 
/// # Errors
/// If, at any point the `callback` returns an error, this function as a whole returns that error.
pub fn iter_bytes_attrs(attrs: Vec<Attribute>, mut callback: impl FnMut(Meta) -> Result<(), Diagnostic>) -> Result<(), Diagnostic> {
    for attr in attrs {
        // Match on the kind of attribute found
        match attr.meta {
            Meta::List(l) => if l.path.is_ident("bytes") {
                // Parse the contents
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
                    callback(arg)?;
                }
            } else {
                continue;
            },

            Meta::Path(_)      |
            Meta::NameValue(_) => { continue; }
        }
    }

    // OK!
    Ok(())
}

/// Parses the toplevel `input`-attribute.
/// 
/// # Arguments
/// - `nv`: The [`MetaNameValue`] that we found.
/// 
/// # Returns
/// The parsed string encoding the input identifier.
/// 
/// # Errors
/// This function may error if the user did not give appropriate input.
#[inline]
pub fn parse_toplevel_input(nv: MetaNameValue) -> Result<LitStr, Diagnostic> {
    let value_span: Span = nv.value.span();
    if let Expr::Lit(ExprLit { attrs: _, lit: Lit::Str(lit) }) = nv.value {
        Ok(lit)
    } else {
        Err(Diagnostic::spanned(value_span, Level::Error, "Expected string literal".into()))
    }
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
pub fn parse_field_attrs(attrs: Vec<Attribute>) -> Result<Option<FieldAttributes>, Diagnostic> {
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
                            return Err(Diagnostic::spanned(nv.path.span(), Level::Error, format!("Unknown field-level `#[bytes(...)]` argument{}", if let Some(ident) = nv.path.get_ident() { format!(" '{ident}'") } else { String::new() })));
                        },

                        // The rest we never match
                        Meta::Path(p) => {
                            return Err(Diagnostic::spanned(p.span(), Level::Error, format!("Unknown field-level `#[bytes(...)]` argument{}", if let Some(ident) = p.get_ident() { format!(" '{ident}'") } else { String::new() })));
                        },
                        Meta::List(l) => {
                            return Err(Diagnostic::spanned(l.path.span(), Level::Error, format!("Unknown field-level `#[bytes(...)]` argument{}", if let Some(ident) = l.path.get_ident() { format!(" '{ident}'") } else { String::new() })));
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

/// Generates the implementation of the fields.
/// 
/// # Arguments
/// - `input_ident`: The name of the input variable as an identifier.
/// - `data`: The [`DataStruct`]-struct containing the fields to parse.
/// 
/// # Returns
/// A tuple with the parser implementations, self-assignment implementations and ParsedLength implementations, respectively.
/// 
/// # Errors
/// This function may error if we failed to parse the field attributes.
pub fn generate_field_impls(input_ident: &Ident, data: DataStruct) -> Result<(Vec<TokenStream2>, Vec<TokenStream2>, Vec<TokenStream2>), Diagnostic> {
    // Next, iterate over all fields to parse those attributes
    let mut fields: Vec<Field> = Vec::with_capacity(data.fields.len());
    for (i, field) in data.fields.into_iter().enumerate() {
        // Parse the identifier of the field
        let ident: Ident = if let Some(field) = field.ident { field } else { Ident::new(&i.to_string(), field.span()) };
        // Parse the type of the identifier
        let ty: Type = field.ty;
        // Parse the attributes of the identifier
        let attrs: Option<FieldAttributes> = parse_field_attrs(field.attrs)?;

        // Combine it into a Field
        fields.push(Field { ident, ty, attrs });
    }

    // Generate the populates of the Self
    let mut parse_impl: Vec<TokenStream2> = Vec::with_capacity(fields.len());
    let mut self_impl: Vec<TokenStream2> = Vec::with_capacity(fields.len());
    let mut add_impl: Vec<TokenStream2> = Vec::with_capacity(fields.len());
    for field in fields {
        let Field { ident, ty, attrs } = field;
        if let Some(attrs) = attrs {
            // Generate some tokens we'll need
            let sident: String = ident.to_string();

            // Create the expressions of the offset & length
            let offset: TokenStream2 = if let Some(offset) = attrs.offset { quote_spanned!{ offset.span() => #offset } } else { quote!{ cumulative_offset } };
            let length: TokenStream2 = if let Some(length) = attrs.length { quote_spanned!{ length.span() => #length } } else { quote!{ <#ty as ::bytes::ParsedLength>::parsed_len(&val) } };

            // Generate parsing the field, but which is based on the dynamicness
            if let Some(dyn_input) = attrs.dynamic {
                parse_impl.push(quote! {
                    let #ident = {
                        // Run the function
                        let offset: ::core::primitive::usize = #offset;
                        let val: #ty = match <#ty as ::bytes::TryFromBytesDynamic<_>>::try_from_bytes_dynamic(#dyn_input, &#input_ident[offset..]) {
                            ::std::result::Result::Ok(val)  => val,
                            ::std::result::Result::Err(err) => { return ::std::result::Result::Err(::bytes::errors::ParseError::Field { name: #sident.into(), err: ::std::boxed::Box::new(err) }); },
                        };

                        // Update the cumulative offset, then return the parsed value
                        cumulative_offset = offset + #length;
                        val
                    };
                });
            } else {
                parse_impl.push(quote! {
                    let #ident = {
                        // Run the function
                        let offset: ::core::primitive::usize = #offset;
                        let val: #ty = match <#ty as ::bytes::TryFromBytes>::try_from_bytes(&#input_ident[offset..]) {
                            ::std::result::Result::Ok(val)  => val,
                            ::std::result::Result::Err(err) => { return ::std::result::Result::Err(::bytes::errors::ParseError::Field { name: #sident.into(), err: ::std::boxed::Box::new(err) }); },
                        };

                        // Update the cumulative offset, then return the parsed value
                        cumulative_offset = offset + #length;
                        val
                    };
                });
            }

            // Generate adding the field to Self and to the parsed count
            self_impl.push(quote! {
                #ident,
            });
            add_impl.push(quote! {
                + <#ty as ::bytes::ParsedLength>::parsed_len(&self.#ident)
            });
        } else {
            // Generate a `Default::default()` instead
            parse_impl.push(quote!{
                let #ident: #ty = ::std::default::Default::default();
            });
            self_impl.push(quote! {
                #ident,
            });
        }
    }

    // Alright return the impls
    Ok((parse_impl, self_impl, add_impl))
}
