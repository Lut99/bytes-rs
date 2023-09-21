//  FLAGS.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 17:11:27
//  Last edited:
//    21 Sep 2023, 14:15:26
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
/// 
/// Implementing this trait for a type automatically derives [`TryFromBytesDynamic`](TryFromBytesDynamic).
/// As such, the functions in this trait define an interface between the automatically derived parser and this type.
/// 
/// # Example
/// ```rust
/// use bytes::{Flags, TryFromBytes as _};
/// 
/// struct CoolFlags {
///     is_cool : bool,
///     is_kind : bool,
///     is_dope : bool,
/// }
/// impl Flags for CoolFlags {
///     fn from_bits(bits: Vec<bool>) -> Self {
///         // Unwrap the list of flags, which should be exactly three long
///         assert_eq!(bits.len(), 3);
///         Self {
///             is_cool : bits[0],
///             is_kind : bits[1],
///             is_dope : bits[2],
///         }
///     }
///     
///     #[inline]
///     fn flag_count() -> usize { 3 }
/// }
/// 
/// assert_eq!(CoolFlags::try_from_bytes(&[ 0b10100000 ]).unwrap().is_dope, true);
/// ```
pub trait Flags {
    /// Constructor for Self that takes the parsed bits.
    /// 
    /// This is meant to be called from the automatically implemented [`TryFromBytesDynamic`] implementation.
    /// It will provide a list with the requested number of bits parsed as booleans, and this function must order
    /// them appropriately for this struct.
    /// 
    /// # Arguments
    /// - `bits`: A vector with the parsed bits as booleans.
    /// 
    /// # Returns
    /// The number of bits parsed.
    /// 
    /// # Panics
    /// This function should panic if the number of bits is not what was requested, which should never happen but just in case.
    /// 
    /// # Example
    /// For an example implementation, see the example given for the [`Flags`]-trait as a whole.
    fn from_bits(bits: Vec<bool>) -> Self;

    /// Returns how many bits we're parsing.
    /// 
    /// This is meant to be called from the automatically implemented [`TryFromBytesDynamic`] implementation to determine
    /// how many bytes to parse. As such, the flag count will automatically round up to the nearest number of bytes (i.e.,
    /// `0` becomes `0` bytes, `1` becomes `1` bytes, `7` becomes `1` bytes, `9` becomes `2` bytes, etc).
    /// 
    /// # Returns
    /// The number of bits to parse.
    /// 
    /// # Example
    /// For an example implementation, see the example given for the [`Flags`]-trait as a whole.
    fn flag_count() -> usize;
}
impl<T: Flags> TryFromBytesDynamic<()> for T {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();

        // Attempt to parse enough bytes
        let n_flags: usize = Self::flag_count();
        let n_bytes: usize = n_flags / 8 + if n_flags % 8 > 0 { 1 } else { 0 };
        if bytes.len() < n_bytes { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: n_bytes }); }

        // Scour them for bits
        let mut bits: Vec<bool> = Vec::with_capacity(n_flags);
        for i in 0..n_flags {
            bits.push(((bytes[i / 8]) >> (7 - i % 8)) & 0x1 == 1);
        }

        // OK done
        Ok(T::from_bits(bits))
    }
}
