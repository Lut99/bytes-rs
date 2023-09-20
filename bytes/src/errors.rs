//  ERRORS.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 13:46:03
//  Last edited:
//    20 Sep 2023, 16:58:03
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
#[derive(Debug)]
pub enum ParseError {
    /// A sub-parser of a field failed.
    Field { name: String, err: Box<dyn Error> },
    /// Input wasn't enough of.
    NotEnoughInput { got: usize, needed: usize },

    /// Given parsed byte was not a valid UTF-8 character
    NonUtf8Char { raw: u32 },
    /// Given byte string was not valid UTF-8.
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
