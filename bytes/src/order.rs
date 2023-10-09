//  ORDER.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 14:39:18
//  Last edited:
//    09 Oct 2023, 11:23:01
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines static structs allowing the use of specific ordering for
//!   parsers.
// 


/***** LIBRARY *****/
/// Abstracts over the various endiannesses.
/// 
/// This enum is meant to be given as dynamic input to dynamically switch
/// between endianness parsing.
/// 
/// # Example
/// ```rust
/// # fn some_condition() -> bool { false }
/// use bytes::{Endianness, TryFromBytesDynamic};
/// 
/// #[derive(TryFromBytesDynamic)]
/// #[bytes(dynamic = "Endianness")]
/// struct Number {
///     #[bytes(dynamic = dynamic_input)]
///     num : u16,
/// }
/// 
/// if some_condition() {
///     assert_eq!(Number::try_from_bytes_dynamic(Endianness::Big, &[ 0x00, 0x2A ]).unwrap().num, 42);
/// } else {
///     assert_eq!(Number::try_from_bytes_dynamic(Endianness::Little, &[ 0x00, 0x2A ]).unwrap().num, 10752);
/// }
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Endianness {
    /// Represents big-endian ordering, i.e., MSB first.
    Big,
    /// Represents little-endian ordering, i.e., LSB first.
    Little,
}
impl From<BigEndian> for Endianness {
    #[inline]
    fn from(_value: BigEndian) -> Self { Self::Big }
}
impl From<LittleEndian> for Endianness {
    #[inline]
    fn from(_value: LittleEndian) -> Self { Self::Little }
}
impl AsRef<Endianness> for Endianness {
    #[inline]
    fn as_ref(&self) -> &Self { self }
}
impl AsMut<Endianness> for Endianness {
    #[inline]
    fn as_mut(&mut self) -> &mut Self { self }
}
impl From<&Endianness> for Endianness {
    #[inline]
    fn from(value: &Self) -> Self { *value }
}
impl From<&mut Endianness> for Endianness {
    #[inline]
    fn from(value: &mut Self) -> Self { *value }
}

/// Instructs a number parser to parse big-endian.
/// 
/// This struct is meant to be given as dynamic input to statically force big-endian parsing for numbers.
/// 
/// # Example
/// ```rust
/// use bytes::{BigEndian, TryFromBytes};
/// 
/// #[derive(TryFromBytes)]
/// struct Number {
///     #[bytes(dynamic = BigEndian)]
///     num : u16,
/// }
/// 
/// assert_eq!(Number::try_from_bytes(&[ 0x00, 0x2A ]).unwrap().num, 42);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct BigEndian;
impl AsRef<BigEndian> for BigEndian {
    #[inline]
    fn as_ref(&self) -> &Self { self }
}
impl AsMut<BigEndian> for BigEndian {
    #[inline]
    fn as_mut(&mut self) -> &mut Self { self }
}
impl From<&BigEndian> for BigEndian {
    #[inline]
    fn from(value: &Self) -> Self { *value }
}
impl From<&mut BigEndian> for BigEndian {
    #[inline]
    fn from(value: &mut Self) -> Self { *value }
}

/// Instructs a number parser to parse little-endian.
/// 
/// This struct is meant to be given as dynamic input to statically force little-endian parsing for numbers.
/// 
/// # Example
/// ```rust
/// use bytes::{LittleEndian, TryFromBytes};
/// 
/// #[derive(TryFromBytes)]
/// struct Number {
///     #[bytes(dynamic = LittleEndian)]
///     num : u16,
/// }
/// 
/// assert_eq!(Number::try_from_bytes(&[ 0x00, 0x2A ]).unwrap().num, 10752);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct LittleEndian;
impl AsRef<LittleEndian> for LittleEndian {
    #[inline]
    fn as_ref(&self) -> &Self { self }
}
impl AsMut<LittleEndian> for LittleEndian {
    #[inline]
    fn as_mut(&mut self) -> &mut Self { self }
}
impl From<&LittleEndian> for LittleEndian {
    #[inline]
    fn from(value: &Self) -> Self { *value }
}
impl From<&mut LittleEndian> for LittleEndian {
    #[inline]
    fn from(value: &mut Self) -> Self { *value }
}
