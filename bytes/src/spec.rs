//  SPEC.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:26:27
//  Last edited:
//    19 Sep 2023, 21:26:43
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the (public) interfaces and structs for this crate.
// 

use std::error::Error;


/***** LIBRARY *****/
/// Defines that a type can be parsed from a series of bytes.
pub trait TryFromBytes: Sized {
    /// Determines what errors this function may throw.
    type Error: Error;


    /// Attempts to parse ourselves from the given bytes.
    /// 
    /// # Arguments
    /// - `bytes`: The [bytes-like](AsRef<[u8]>) object to parse.
    /// 
    /// # Returns
    /// A new instance of Self parsed from the given bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to parse the given bytes as ourselves.
    fn try_from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error>;
}
