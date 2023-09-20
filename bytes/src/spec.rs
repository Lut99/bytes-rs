//  SPEC.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:26:27
//  Last edited:
//    20 Sep 2023, 17:30:42
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the (public) interfaces and structs for this crate.
// 

use std::borrow::Cow;
use std::error::Error;
use std::mem::size_of;

use crate::errors::ParseError;
use crate::order::{BigEndian, Endianness, LittleEndian};
use crate::string::{Lossiness, Lossy, NonLossy};


/***** AUXILLARY *****/
/// Defines some types that can be used to pass sizes to some parsers.
pub trait Counting {
    /// Returns the count embedded in this struct.
    /// 
    /// # Returns
    /// The number of bytes/elements to parse (depends on the parser this is given to).
    /// 
    /// # Panics
    /// This function is allowed to panic if it likes.
    fn count(&self) -> usize;
}
impl Counting for usize {
    #[inline]
    fn count(&self) -> usize { *self }
}
impl<C: Counting> Counting for (C,) {
    #[inline]
    fn count(&self) -> usize { self.0.count() }
}
impl<C: Counting, T2> Counting for (C, T2) {
    #[inline]
    fn count(&self) -> usize { self.0.count() }
}
impl<C: Counting, T2, T3> Counting for (C, T2, T3) {
    #[inline]
    fn count(&self) -> usize { self.0.count() }
}
impl<C: Counting, T2, T3, T4> Counting for (C, T2, T3, T4) {
    #[inline]
    fn count(&self) -> usize { self.0.count() }
}
impl<C: Counting, T2, T3, T4, T5> Counting for (C, T2, T3, T4, T5) {
    #[inline]
    fn count(&self) -> usize { self.0.count() }
}
impl<C: Counting, T2, T3, T4, T5, T6> Counting for (C, T2, T3, T4, T5, T6) {
    #[inline]
    fn count(&self) -> usize { self.0.count() }
}
impl<C: Counting, T2, T3, T4, T5, T6, T7> Counting for (C, T2, T3, T4, T5, T6, T7) {
    #[inline]
    fn count(&self) -> usize { self.0.count() }
}





/***** LIBRARY *****/
/// Defines that a type can be parsed from a series of bytes.
pub trait TryFromBytes: TryFromBytesDynamic<()> {
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
impl<T: TryFromBytesDynamic<()>> TryFromBytes for T {
    #[inline]
    #[track_caller]
    fn try_from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> { Self::try_from_bytes_dynamic((), bytes) }
}



/// Defines that a type can be parsed from a series of bytes, but requires additional input to do so.
pub trait TryFromBytesDynamic<I>: Sized {
    /// Determines what errors this function may throw.
    type Error: Error;


    /// Attempts to parse ourselves from the given input and bytes.
    /// 
    /// # Arguments
    /// - `input`: The additional input needed to make sense of this, like some length.
    /// - `bytes`: The [bytes-like](AsRef<[u8]>) object to parse.
    /// 
    /// # Returns
    /// A new instance of Self parsed from the given bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to parse the given bytes as ourselves.
    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error>;
}

// Implement it for primitives
impl TryFromBytesDynamic<()> for u8 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();
        if !bytes.is_empty() {
            Ok(bytes[0])
        } else {
            Err(ParseError::NotEnoughInput { got: 0, needed: 1 })
        }
    }
}
impl TryFromBytesDynamic<()> for i8 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();
        if !bytes.is_empty() {
            Ok(bytes[0] as i8)
        } else {
            Err(ParseError::NotEnoughInput { got: 0, needed: 1 })
        }
    }
}
impl TryFromBytesDynamic<()> for u16 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for u16 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for u16 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for u16 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for i16 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for i16 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for i16 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for i16 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for u32 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for u32 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for u32 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for u32 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for i32 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for i32 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for i32 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for i32 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for u64 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for u64 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for u64 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for u64 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for i64 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for i64 {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for i64 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for i64 {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for usize {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for usize {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for usize {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for usize {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for isize {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<Endianness> for isize {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for isize {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<LittleEndian> for isize {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();

        // Assert the length checks out
        if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
        else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
        Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
    }
}
impl TryFromBytesDynamic<()> for char {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        // Parse the input as a u32 first
        let raw: u32 = u32::try_from_bytes_dynamic(input, bytes)?;
        match Self::from_u32(raw) {
            Some(val) => Ok(val),
            None      => Err(ParseError::NonUtf8Char { raw }),
        }
    }
}
impl TryFromBytesDynamic<Endianness> for char {
    type Error = crate::errors::ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
        }
    }
}
impl TryFromBytesDynamic<BigEndian> for char {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        // Parse the input as a u32 first
        let raw: u32 = u32::try_from_bytes_dynamic(input, bytes)?;
        match Self::from_u32(raw) {
            Some(val) => Ok(val),
            None      => Err(ParseError::NonUtf8Char { raw }),
        }
    }
}
impl TryFromBytesDynamic<LittleEndian> for char {
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        // Parse the input as a u32 first
        let raw: u32 = u32::try_from_bytes_dynamic(input, bytes)?;
        match Self::from_u32(raw) {
            Some(val) => Ok(val),
            None      => Err(ParseError::NonUtf8Char { raw }),
        }
    }
}

// Implement for tightly-packed containers
impl<I> TryFromBytesDynamic<I> for () {
    type Error = std::convert::Infallible;

    #[inline]
    fn try_from_bytes_dynamic(_input: I, _bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> { Ok(()) }
}
impl<T: TryFromBytesDynamic<I>, I> TryFromBytesDynamic<I> for (T,)
where
    T::Error: 'static,
{
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        Ok((
            T::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
        ))
    }
}
impl<T1: ParsedLength + TryFromBytesDynamic<I>, T2: TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for (T1,T2)
where
    T1::Error: 'static,
    T2::Error: 'static,
{
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();
        Ok((
            T1::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
            T2::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
        ))
    }
}
impl<T1: ParsedLength + TryFromBytesDynamic<I>, T2: ParsedLength + TryFromBytesDynamic<I>, T3: TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for (T1,T2,T3)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
{
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();
        Ok((
            T1::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
            T2::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
            T3::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
        ))
    }
}
impl<T1: ParsedLength + TryFromBytesDynamic<I>, T2: ParsedLength + TryFromBytesDynamic<I>, T3: ParsedLength + TryFromBytesDynamic<I>, T4: TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for (T1,T2,T3,T4)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
{
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();
        Ok((
            T1::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
            T2::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
            T3::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
            T4::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
        ))
    }
}
impl<T1: ParsedLength + TryFromBytesDynamic<I>, T2: ParsedLength + TryFromBytesDynamic<I>, T3: ParsedLength + TryFromBytesDynamic<I>, T4: ParsedLength + TryFromBytesDynamic<I>, T5: TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for (T1,T2,T3,T4,T5)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
{
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();
        Ok((
            T1::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
            T2::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
            T3::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
            T4::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
            T5::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
        ))
    }
}
impl<T1: ParsedLength + TryFromBytesDynamic<I>, T2: ParsedLength + TryFromBytesDynamic<I>, T3: ParsedLength + TryFromBytesDynamic<I>, T4: ParsedLength + TryFromBytesDynamic<I>, T5: ParsedLength + TryFromBytesDynamic<I>, T6: TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for (T1,T2,T3,T4,T5,T6)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
    T6::Error: 'static,
{
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();
        Ok((
            T1::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
            T2::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
            T3::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
            T4::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
            T5::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
            T6::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "5".into(), err: Box::new(err) })?,
        ))
    }
}
impl<T1: ParsedLength + TryFromBytesDynamic<I>, T2: ParsedLength + TryFromBytesDynamic<I>, T3: ParsedLength + TryFromBytesDynamic<I>, T4: ParsedLength + TryFromBytesDynamic<I>, T5: ParsedLength + TryFromBytesDynamic<I>, T6: ParsedLength + TryFromBytesDynamic<I>, T7: TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for (T1,T2,T3,T4,T5,T6,T7)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
    T6::Error: 'static,
    T7::Error: 'static,
{
    type Error = crate::errors::ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let mut bytes: &[u8] = bytes.as_ref();
        Ok((
            T1::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
            T2::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
            T3::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
            T4::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
            T5::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
            T6::try_from_bytes_dynamic(input.clone(), bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "5".into(), err: Box::new(err) })?,
            T7::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "6".into(), err: Box::new(err) })?,
        ))
    }
}
impl<const LEN: usize, T: ParsedLength + TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for [ T; LEN ]
where
    T::Error: 'static,
{
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        // Parse them all, Pokémon
        let mut bytes: &[u8] = bytes.as_ref();
        let mut res: [ Option<T>; LEN ] = std::array::from_fn(|_| None);
        for (i, e) in res.iter_mut().enumerate() {
            // Parse the element
            let val: T = match T::try_from_bytes_dynamic(input.clone(), bytes) {
                Ok(val)  => val,
                Err(err) => { return Err(ParseError::Field { name: format!("[{i}]"), err: Box::new(err) }); },
            };

            // Update the offset, then continue
            bytes = &bytes[val.parsed_len()..];
            *e = Some(val);
        }

        // Alright, return the mapped version
        Ok(res.map(|e| e.unwrap()))
    }
}
impl<T: ParsedLength + TryFromBytesDynamic<I>, I: Clone + Counting> TryFromBytesDynamic<I> for Vec<T>
where
    T::Error: 'static,
{
    type Error = ParseError;

    fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        // Get the count from the input
        let count: usize = input.count();

        // Construct the list
        let mut bytes: &[u8] = bytes.as_ref();
        let mut res: Vec<T> = Vec::with_capacity(count);
        for i in 0..count {
            // Parse the element
            let val: T = match T::try_from_bytes_dynamic(input.clone(), bytes) {
                Ok(val)  => val,
                Err(err) => { return Err(ParseError::Field { name: format!("[{i}]"), err: Box::new(err) }); },
            };

            // Update the offset, then continue
            bytes = &bytes[val.parsed_len()..];
            res.push(val);
        }

        // Done, return the vector
        Ok(res)
    }
}

// Implement for string-like
impl TryFromBytesDynamic<usize> for Cow<'_, str> {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: usize, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(NonLossy(input), bytes)
    }
}
impl TryFromBytesDynamic<Lossiness> for Cow<'_, str> {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Lossiness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Lossiness::Lossy(l)    => Self::try_from_bytes_dynamic(l, bytes),
            Lossiness::NonLossy(n) => Self::try_from_bytes_dynamic(n, bytes),
        }        
    }
}
impl TryFromBytesDynamic<Lossy> for Cow<'_, str> {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Lossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();

        // Attempt to take a large enough slice
        if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
        let bytes: &[u8] = &bytes[..input.0];

        // Next, attempt to convert it to a string
        Ok(Cow::Owned(String::from_utf8_lossy(bytes).to_string()))
    }
}
impl TryFromBytesDynamic<NonLossy> for Cow<'_, str> {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: NonLossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();

        // Attempt to take a large enough slice
        if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
        let bytes: &[u8] = &bytes[..input.0];

        // Next, attempt to convert it to a string
        match String::from_utf8(bytes.into()) {
            Ok(val)  => Ok(Cow::Owned(val)),
            Err(err) => Err(ParseError::NonUtf8String { err }),
        }
    }
}
impl TryFromBytesDynamic<usize> for String {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: usize, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(NonLossy(input), bytes)
    }
}
impl TryFromBytesDynamic<Lossiness> for String {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Lossiness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        match input {
            Lossiness::Lossy(l)    => Self::try_from_bytes_dynamic(l, bytes),
            Lossiness::NonLossy(n) => Self::try_from_bytes_dynamic(n, bytes),
        }        
    }
}
impl TryFromBytesDynamic<Lossy> for String {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: Lossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();

        // Attempt to take a large enough slice
        if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
        let bytes: &[u8] = &bytes[..input.0];

        // Next, attempt to convert it to a string
        Ok(String::from_utf8_lossy(bytes).into_owned())
    }
}
impl TryFromBytesDynamic<NonLossy> for String {
    type Error = ParseError;

    #[inline]
    fn try_from_bytes_dynamic(input: NonLossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
        let bytes: &[u8] = bytes.as_ref();

        // Attempt to take a large enough slice
        if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
        let bytes: &[u8] = &bytes[..input.0];

        // Next, attempt to convert it to a string
        match String::from_utf8(bytes.into()) {
            Ok(val)  => Ok(val),
            Err(err) => Err(ParseError::NonUtf8String { err }),
        }
    }
}



/// States that a type has a parsed length.
pub trait ParsedLength {
    /// Returns the number of bytes parsed in this type.
    /// 
    /// # Returns
    /// The number of bytes that were parsed.
    /// 
    /// # Panics
    /// This function is allowed to panic if this cannot be known.
    fn parsed_len(&self) -> usize;
}

// Implement it for primitives
impl ParsedLength for u8 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for i8 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for u16 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for i16 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for u32 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for i32 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for u64 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for i64 {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for usize {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for isize {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}
impl ParsedLength for char {
    #[inline]
    fn parsed_len(&self) -> usize { size_of::<Self>() }
}

// Implement for tightly-packed containers
impl ParsedLength for () {
    #[inline]
    fn parsed_len(&self) -> usize { 0 }
}
impl<T: ParsedLength> ParsedLength for (T,) {
    #[inline]
    fn parsed_len(&self) -> usize { self.0.parsed_len() }
}
impl<T1: ParsedLength, T2: ParsedLength> ParsedLength for (T1,T2) {
    #[inline]
    fn parsed_len(&self) -> usize { self.0.parsed_len() + self.1.parsed_len() }
}
impl<T1: ParsedLength, T2: ParsedLength, T3: ParsedLength> ParsedLength for (T1,T2,T3) {
    #[inline]
    fn parsed_len(&self) -> usize { self.0.parsed_len() + self.1.parsed_len() + self.2.parsed_len() }
}
impl<T1: ParsedLength, T2: ParsedLength, T3: ParsedLength, T4: ParsedLength> ParsedLength for (T1,T2,T3,T4) {
    #[inline]
    fn parsed_len(&self) -> usize { self.0.parsed_len() + self.1.parsed_len() + self.2.parsed_len() + self.3.parsed_len() }
}
impl<T1: ParsedLength, T2: ParsedLength, T3: ParsedLength, T4: ParsedLength, T5: ParsedLength> ParsedLength for (T1,T2,T3,T4,T5) {
    #[inline]
    fn parsed_len(&self) -> usize { self.0.parsed_len() + self.1.parsed_len() + self.2.parsed_len() + self.3.parsed_len() + self.4.parsed_len() }
}
impl<T1: ParsedLength, T2: ParsedLength, T3: ParsedLength, T4: ParsedLength, T5: ParsedLength, T6: ParsedLength> ParsedLength for (T1,T2,T3,T4,T5,T6) {
    #[inline]
    fn parsed_len(&self) -> usize { self.0.parsed_len() + self.1.parsed_len() + self.2.parsed_len() + self.3.parsed_len() + self.4.parsed_len() + self.5.parsed_len() }
}
impl<T1: ParsedLength, T2: ParsedLength, T3: ParsedLength, T4: ParsedLength, T5: ParsedLength, T6: ParsedLength, T7: ParsedLength> ParsedLength for (T1,T2,T3,T4,T5,T6,T7) {
    #[inline]
    fn parsed_len(&self) -> usize { self.0.parsed_len() + self.1.parsed_len() + self.2.parsed_len() + self.3.parsed_len() + self.4.parsed_len() + self.5.parsed_len() + self.6.parsed_len() }
}
impl<const LEN: usize, T: ParsedLength> ParsedLength for [ T; LEN ] {
    #[inline]
    fn parsed_len(&self) -> usize {
        self.iter().map(|e| e.parsed_len()).sum()
    }
}
impl<T: ParsedLength> ParsedLength for [T] {
    #[inline]
    fn parsed_len(&self) -> usize {
        self.iter().map(|e| e.parsed_len()).sum()
    }
}
impl<T: ParsedLength> ParsedLength for Vec<T> {
    #[inline]
    fn parsed_len(&self) -> usize {
        self.iter().map(|e| e.parsed_len()).sum()
    }
}

// Implement for string-like
impl ParsedLength for str {
    #[inline]
    fn parsed_len(&self) -> usize { self.len() }
}
impl ParsedLength for Cow<'_, str> {
    #[inline]
    fn parsed_len(&self) -> usize { self.len() }
}
impl ParsedLength for String {
    #[inline]
    fn parsed_len(&self) -> usize { self.len() }
}

// Implement for all references
impl<T: ParsedLength> ParsedLength for &T {
    #[inline]
    fn parsed_len(&self) -> usize { (**self).parsed_len() }
}
impl<T: ParsedLength> ParsedLength for &mut T {
    #[inline]
    fn parsed_len(&self) -> usize { (**self).parsed_len() }
}
