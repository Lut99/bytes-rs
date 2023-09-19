//  TRY FROM BYTES.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:09:49
//  Last edited:
//    19 Sep 2023, 21:22:24
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the derivation procedure for the [`TryFromBytes`].
// 

use proc_macro::TokenStream;
use proc_macro_error::{Diagnostic, Level};
use syn::{Attribute, Data, DataStruct, Generics, Ident, Meta, Visibility};
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
/// A new [`FieldAttributes`] representing the parsed information.
fn parse_field_attrs(attrs: Vec<Attribute>) -> Result<FieldAttributes, Diagnostic> {
    let res: FieldAttributes = Default::default();
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
    
}
impl Default for FieldAttributes {
    fn default() -> Self {
        Self {
            
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
    let mut field_attrs: Vec<FieldAttributes> = Vec::with_capacity(data.fields.len());
    for field in data.fields {
        field_attrs.push(parse_field_attrs(field.attrs)?);
    }

    // OK, done
    Ok(quote!{}.into())
}
