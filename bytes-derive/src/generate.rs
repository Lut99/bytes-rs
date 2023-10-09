//  GENERATE.rs
//    by Lut99
// 
//  Created:
//    02 Oct 2023, 19:52:06
//  Last edited:
//    09 Oct 2023, 19:18:08
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines functions for generating the derive impls.
// 

use proc_macro2::TokenStream as TokenStream2;
use syn::{Expr, Generics, Ident, Type};
use quote::quote;

use crate::spec::{TryFromBytesDynamicInfo, TryToBytesDynamicInfo};


/***** LIBRARY *****/
/// Generates the derive implementation for `TryFromBytesDynamic`.
/// 
/// # Arguments
/// - `generics`: The derive type generics to add to any implementation.
/// - `info`: The [`TryFromBytesDynamicInfo`] struct that describes what to generate.
/// 
/// # Returns
/// A [`TokenStream2`] that contains the generated tokens.
pub fn generate_parser(generics: Generics, info: TryFromBytesDynamicInfo) -> TokenStream2 {
    // Generate the implementations for all fields first
    // let mut needs_cursor: bool = false;
    let mut parse_impls: Vec<TokenStream2> = Vec::with_capacity(info.fields.len());
    let mut self_impls: Vec<TokenStream2> = Vec::with_capacity(info.fields.len());
    for field in info.fields {
        // Fetch the common things we need
        let real_name: Ident = field.common.real_name;
        let dyn_name: Ident = field.common.dyn_name;
        let real_ty: Type = field.common.real_ty;
        let parse_ty: Type = field.common.parse_ty.0;

        // Match on enabled or not
        if field.common.enabled {
            // Fetch the specific things we need
            let real_name_str: String = real_name.to_string();
            let input_name: &Ident = &info.metadata.input_name;
            let input: Expr = field.common.input;

            // // Generate an offset impl, if necessary
            // let offset: Option<TokenStream2> = field.common.offset.map(|offset| {
            //     // Mark that we need the cursor
            //     needs_cursor = true;

            //     // Generate the moving part
            //     quote! {
            //         // Offset the input
            //         if let ::std::result::Result::Err(err) = <::std::io::Cursor<_> as ::std::io::Seek>::seek(::std::io::SeekFrom::Start(#offset)) {
            //             return ::std::result::Result::Err(::bytes::from_bytes::Error::Seek { err });
            //         }
            //     }
            // });
            let offset: Option<TokenStream2> = None;

            // Generate the parser code...
            parse_impls.push(quote! {
                let #dyn_name: #real_ty = {
                    #offset

                    // Attempt to parse using the dynamic type
                    match <#parse_ty as ::bytes::from_bytes::TryFromBytesDynamic<_>>::try_from_bytes_dynamic(#input, &mut #input_name) {
                        ::std::result::Result::Ok(val) => val.into(),
                        ::std::result::Result::Err(err) => { return ::std::result::Result::Err(::bytes::from_bytes::Error::Field { name: #real_name_str.into(), err: ::std::boxed::Box::new(err) }); },
                    }
                };
            });
        } else {
            // Generate a default impl instead
            parse_impls.push(quote! {
                let #dyn_name: #real_ty = <#parse_ty as ::std::default::Default>::default().into();
            });
        }

        // ...and the self code!
        self_impls.push(quote! {
            #real_name : #dyn_name,
        });
    }

    // Fetch some main implementation curiosa
    let name: Ident = info.metadata.name;
    let input_name: Ident = info.metadata.input_name;
    let dynamic_name: Ident = info.metadata.dynamic_name;
    let dynamic_ty: Type = info.metadata.dynamic_ty.0;

    // // Generate wrapping the reader in a cursor
    // let cursor: Option<TokenStream2> = if needs_cursor {
    //     Some(quote! {
    //         // Wrap the input in a cursor so we can offset
    //         let mut #input_name: ::std::io::Cursor<_> = ::std::io::Cursor::new(#input_name);
    //     })
    // } else {
    //     None
    // };
    let cursor: Option<TokenStream2> = None;

    // Next, generate the main implementation
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let parser_impl: TokenStream2 = quote! {
        #[automatically_derived]
        impl #impl_generics ::bytes::from_bytes::TryFromBytesDynamic<#dynamic_ty> for #name #ty_generics #where_clause {
            type Error = ::bytes::from_bytes::Error;

            fn try_from_bytes_dynamic(#dynamic_name: #dynamic_ty, mut #input_name: impl ::std::io::Read) -> ::std::result::Result<Self, Self::Error> {
                #cursor

                // Start parsing each of the types
                #(#parse_impls)*

                // OK, build self
                Ok(Self {
                    #(#self_impls)*
                })
            }
        }
    };

    // If told to do so, generate refs
    let full_impl: TokenStream2 = if info.metadata.generate_refs {
        quote! {
            #parser_impl

            #[automatically_derived]
            impl #impl_generics ::bytes::from_bytes::TryFromBytesDynamic<&#dynamic_ty> for #name #ty_generics #where_clause {
                type Error = ::bytes::from_bytes::Error;
    
                fn try_from_bytes_dynamic(#dynamic_name: &#dynamic_ty, mut #input_name: impl ::std::io::Read) -> ::std::result::Result<Self, Self::Error> {
                    // Refer to the main impl
                    Self::try_from_bytes_dynamic(<&#dynamic_ty as ::std::clone::Clone>::clone(&#dynamic_name), #input_name)
                }
            }
        }
    } else {
        parser_impl
    };

    // Done!
    full_impl
}



/// Generates the derive implementation for `TryToBytesDynamic`.
/// 
/// # Arguments
/// - `generics`: The derive type generics to add to any implementation.
/// - `info`: The [`TryToBytesDynamicInfo`] struct that describes what to generate.
/// 
/// # Returns
/// A [`TokenStream2`] that contains the generated tokens.
pub fn generate_serializer(generics: Generics, info: TryToBytesDynamicInfo) -> TokenStream2 {
    // Generate the implementations for all fields first
    // let mut needs_cursor: bool = false;
    let mut self_impls: Vec<TokenStream2> = Vec::with_capacity(info.fields.len());
    let mut serialize_impls: Vec<TokenStream2> = Vec::with_capacity(info.fields.len());
    for field in info.fields {
        // Fetch the common things we need
        let real_name: Ident = field.common.real_name;
        let dyn_name: Ident = field.common.dyn_name;

        // Add the field, then quit if not serializing
        self_impls.push(quote!{
            let #dyn_name = &self.#real_name;
        });
        if !field.common.enabled { continue; }

        // Fetch the specific things we need
        let real_name_str: String = real_name.to_string();
        let real_ty: Type = field.common.real_ty;
        let input_name: &Ident = &info.metadata.input_name;
        let input: Expr = field.common.input;

        // // Generate an offset impl, if necessary
        // let offset: Option<TokenStream2> = field.common.offset.map(|offset| {
        //     // Mark that we need the cursor
        //     needs_cursor = true;

        //     // Generate the moving part
        //     quote! {
        //         // Offset the input
        //         if let ::std::result::Result::Err(err) = <::std::io::Cursor<_> as ::std::io::Seek>::seek(::std::io::SeekFrom::Start(#offset)) {
        //             return ::std::result::Result::Err(::bytes::to_bytes::Error::Seek { err });
        //         }
        //     }
        // });
        let offset: Option<TokenStream2> = None;

        // Generate the parser code...
        serialize_impls.push(quote! {
            #offset

            // Attempt to serialize using the dynamic type
            if let ::std::result::Result::Err(err) = <#real_ty as ::bytes::to_bytes::TryToBytesDynamic<_>>::try_to_bytes_dynamic(#dyn_name, #input, &mut #input_name) {
                return ::std::result::Result::Err(::bytes::to_bytes::Error::Field { name: #real_name_str.into(), err: ::std::boxed::Box::new(err) });
            }
        });
    }

    // Fetch some main implementation curiosa
    let name: Ident = info.metadata.name;
    let input_name: Ident = info.metadata.input_name;
    let dynamic_name: Ident = info.metadata.dynamic_name;
    let dynamic_ty: Type = info.metadata.dynamic_ty.0;

    // // Generate wrapping the reader in a cursor
    // let cursor: Option<TokenStream2> = if needs_cursor {
    //     Some(quote! {
    //         // Wrap the input in a cursor so we can offset
    //         let mut #input_name: ::std::io::Cursor<_> = ::std::io::Cursor::new(#input_name);
    //     })
    // } else {
    //     None
    // };
    let cursor: Option<TokenStream2> = None;

    // Next, generate the main implementation
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let parser_impl: TokenStream2 = quote! {
        #[automatically_derived]
        impl #impl_generics ::bytes::to_bytes::TryToBytesDynamic<#dynamic_ty> for #name #ty_generics #where_clause {
            type Error = ::bytes::to_bytes::Error;

            fn try_to_bytes_dynamic(&self, #dynamic_name: #dynamic_ty, mut #input_name: impl ::std::io::Write) -> ::std::result::Result<(), Self::Error> {
                #cursor

                // Unwrap ourselves to refer to in expressions
                #(#self_impls)*

                // Start parsing each of the types
                #(#serialize_impls)*

                // Done!
                Ok(())
            }
        }
    };

    // If told to do so, generate refs
    let full_impl: TokenStream2 = if info.metadata.generate_refs {
        quote! {
            #parser_impl

            #[automatically_derived]
            impl #impl_generics ::bytes::to_bytes::TryToBytesDynamic<&#dynamic_ty> for #name #ty_generics #where_clause {
                type Error = ::bytes::to_bytes::Error;

                #[inline]
                fn try_to_bytes_dynamic(&self, #dynamic_name: &#dynamic_ty, mut #input_name: impl ::std::io::Write) -> ::std::result::Result<(), Self::Error> {
                    // Refer to the main implementation using a clone
                    self.try_to_bytes_dynamic(<&#dynamic_ty as ::std::clone::Clone>::clone(&#dynamic_name), #input_name)
                }
            }
        }
    } else {
        parser_impl
    };

    // Done!
    full_impl
}
