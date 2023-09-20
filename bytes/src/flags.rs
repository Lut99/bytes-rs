//  FLAGS.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 17:11:27
//  Last edited:
//    20 Sep 2023, 17:23:06
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines a special parsable type for parsing bytes as a series of
//!   flags.
// 

use crate::errors::ParseError;
use crate::spec::TryFromBytesDynamic;


/***** LIBRARY *****/
/// A special trait that eases implementing a type containing only flags.
pub trait Flags {
    /// Constructor for Self that takes the parsed bits.
    /// 
    /// # Arguments
    /// - `bits`: A vector with the parsed bits as booleans.
    /// 
    /// # Returns
    /// The number of bits parsed.
    /// 
    /// # Panics
    /// This function should panic if the number of bits is not what was requested, which should never happen but just in case.
    fn from_bits(bits: Vec<bool>) -> Self;

    /// Returns how many bits we're parsing.
    /// 
    /// The lowest number of bytes are parsed that can accomodate this number.
    /// 
    /// # Returns
    /// The number of bits to parse.
    fn flag_count() -> usize;
}
impl<T: Flags> TryFromBytesDynamic<()> for T {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();

        // Attempt to parse enough bytes
        let n_flags: usize = Self::flag_count();
        let n_bytes: usize = if n_flags > 0 { 1 + n_flags / 8 } else { 0 };
        if bytes.len() < n_bytes { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: n_bytes }); }

        // Scour them for bits
        let mut bits: Vec<bool> = Vec::with_capacity(n_flags);
        for i in 0..n_flags {
            bits.push(((bytes[if i > 0 { 1 + i / 8 } else { 0 }]) >> (7 - i % 8)) & 0x1 == 1);
        }

        // OK done
        Ok(T::from_bits(bits))
    }
}

// Implement for some boolean things
impl Flags for bool {
    fn from_bits(bits: Vec<bool>) -> Self {
        if bits.len() != 1 { panic!("Requested 1 bit from Flags implementation, got {}", bits.len()); }
        *bits.first().unwrap()
    }

    #[inline]
    fn flag_count() -> usize { 1 }
}
