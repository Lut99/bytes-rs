//  ERRORS.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 13:46:03
//  Last edited:
//    27 Sep 2023, 18:11:46
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines errors originating from the `bytes` crate.
// 

use std::error::Error;
use std::fmt::{Display, Formatter, Result as FResult};


/***** LIBRARY *****/
/// Defines errors that may occur when using library parsers.
/// 
/// Note that this struct is designed to report nested errors only when [`source()`](Error::source()) is called.
/// As such, consider using a library for reporting these easily (e.g., <https://github.com/Lut99/error-trace-rs>).
#[derive(Debug)]
pub enum ParseError {
    /// A sub-parser of a field failed.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes;
    /// use bytes::errors::ParseError;
    /// 
    /// #[derive(TryFromBytes)]
    /// struct Example {
    ///     #[bytes]
    ///     field_1 : u32
    /// }
    /// 
    /// assert!(matches!(Example::try_from_bytes(&[]), Err(ParseError::Field{ .. })));
    /// ```
    Field { name: String, err: Box<dyn Error> },
    /// Input wasn't enough of.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::errors::ParseError;
    /// 
    /// assert!(matches!(u32::try_from_bytes(&[]), Err(ParseError::NotEnoughInput { got: 0, needed: 4 })));
    /// ```
    NotEnoughInput { got: usize, needed: usize },

    /// Given parsed byte was not a valid UTF-8 character.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::errors::ParseError;
    /// 
    /// assert!(matches!(char::try_from_bytes(&[ 0x00, 0x00, 0x00, 0xFF ]), Err(ParseError::NonUtf8Char { .. })));
    /// ```
    NonUtf8Char { raw: u32 },
    /// Given byte string was not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytesDynamic as _;
    /// use bytes::errors::ParseError;
    /// 
    /// assert!(matches!(String::try_from_bytes_dynamic(4, &[ 0x00, 0x00, 0x00, 0xFF ]), Err(ParseError::NonUtf8String { .. })));
    /// ```
    NonUtf8String { err: std::string::FromUtf8Error },
}
impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use ParseError::*;
        match self {
            Field { name, .. }             => write!(f, "Failed to parse field '{name}'"),
            NotEnoughInput { got, needed } => write!(f, "Not enough input (got {got} bytes, needed {needed} bytes)"),

            NonUtf8Char { raw }  => write!(f, "Byte '{raw:#010X}' is not a valid UTF-8 character"),
            NonUtf8String { .. } => write!(f, "Given bytes are not valid UTF-8"),
        }
    }
}
impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        use ParseError::*;
        match self {
            Field { err, .. }     => Some(&**err),
            NotEnoughInput { .. } => None,

            NonUtf8Char { .. }    => None,
            NonUtf8String { err } => Some(err),
        }
    }
}



/// Defines errors that may occur when using library serializers.
/// 
/// Note that this struct is designed to report nested errors only when [`source()`](Error::source()) is called.
/// As such, consider using a library for reporting these easily (e.g., <https://github.com/Lut99/error-trace-rs>).
#[derive(Debug)]
pub enum SerializeError {
    /// Couldn't write to the given writer.
    Writer { err: std::io::Error },
}
impl Display for SerializeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use SerializeError::*;
        match self {
            Writer { .. } => write!(f, "Failed to write to given writer"),
        }
    }
}
impl Error for SerializeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        use SerializeError::*;
        match self {
            Writer { err } => Some(err),
        }
    }
}
