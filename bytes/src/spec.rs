//  SPEC.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:26:27
//  Last edited:
//    29 Sep 2023, 21:48:58
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the (public) interfaces and structs for this crate.
// 

use std::borrow::Cow;
use std::error::Error;
use std::io::{Read, Write};
use std::mem::size_of;

use crate::errors::{ParseError, SerializeError};
use crate::order::{BigEndian, Endianness, LittleEndian};
use crate::string::{Lossiness, Lossy, NonLossy};


/***** HELPERS *****/
/// Helper trait for selecting which types we mean when we implement [`TryFromBytesDynamic`] for primitives.
trait PrimitiveFromBytes: num_traits::FromBytes {}
impl PrimitiveFromBytes for u8 {}
impl PrimitiveFromBytes for i8 {}
impl PrimitiveFromBytes for u16 {}
impl PrimitiveFromBytes for i16 {}
impl PrimitiveFromBytes for u32 {}
impl PrimitiveFromBytes for i32 {}
impl PrimitiveFromBytes for u64 {}
impl PrimitiveFromBytes for i64 {}
impl PrimitiveFromBytes for u128 {}
impl PrimitiveFromBytes for i128 {}
impl PrimitiveFromBytes for usize {}
impl PrimitiveFromBytes for isize {}
impl PrimitiveFromBytes for f32 {}
impl PrimitiveFromBytes for f64 {}



/// Helper trait for selecting which types we mean when we implement [`TryToBytesDynamic`] for primitives.
trait PrimitiveToBytes: num_traits::ToBytes {}
impl PrimitiveToBytes for u8 {}
impl PrimitiveToBytes for i8 {}
impl PrimitiveToBytes for u16 {}
impl PrimitiveToBytes for i16 {}
impl PrimitiveToBytes for u32 {}
impl PrimitiveToBytes for i32 {}
impl PrimitiveToBytes for u64 {}
impl PrimitiveToBytes for i64 {}
impl PrimitiveToBytes for u128 {}
impl PrimitiveToBytes for i128 {}
impl PrimitiveToBytes for usize {}
impl PrimitiveToBytes for isize {}
impl PrimitiveToBytes for f32 {}
impl PrimitiveToBytes for f64 {}





/***** LIBRARY *****/
/// Defines that a type can be parsed from a series of bytes.
/// 
/// This can be thought of as a non-configurable counterpart to the [`TryFromBytesDynamic`].
/// In fact, it is implemented as a more convenient alias for a dynamic implementation that takes `()` as input.
/// 
/// Typically, you can automatically derive this trait using the [`TryFromBytes`](crate::procedural::TryFromBytes)-macro.
/// 
/// # Example
/// ```rust
/// use bytes::{TryFromBytes as _, TryFromBytesDynamic};
/// 
/// struct Example {
///     num : u16,
/// }
/// impl TryFromBytesDynamic<()> for Example {
///     type Error = bytes::errors::ParseError;
/// 
///     #[inline]
///     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
///         Ok(Self {
///             num : u16::try_from_bytes_dynamic(input, bytes)?,
///         })
///     }
/// }
/// 
/// assert_eq!(Example::try_from_bytes_dynamic((), &[ 0x00, 0x2A ]).unwrap().num, 10752);
/// // Equivalent and more convenient
/// assert_eq!(Example::try_from_bytes(&[ 0x00, 0x2A ]).unwrap().num, 10752);
/// ```
pub trait TryFromBytes: TryFromBytesDynamic<()> {
    /// Attempts to parse ourselves from the given bytes.
    /// 
    /// # Arguments
    /// - `reader`: The [`Read`]er object to parse from.
    /// 
    /// # Returns
    /// A new instance of Self parsed from the given bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to parse the given bytes as ourselves.
    /// 
    /// # Examples
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// 
    /// assert_eq!(u8::try_from_bytes(&[ 0x2A ]).unwrap(), 42);
    /// assert_eq!(i16::try_from_bytes(&[ 0x2A, 0x00 ]).unwrap(), 42);
    /// assert_eq!(<(u8, u8)>::try_from_bytes(&[ 0x00, 0x2A ]).unwrap(), (0, 42));
    /// ```
    fn try_from_bytes(bytes: impl Read) -> Result<Self, Self::Error>;
}
impl<T: TryFromBytesDynamic<()>> TryFromBytes for T {
    /// Automatic implementation of `TryFromBytes` for [`TryFromBytesDynamic`]'s that take no input (`()`).
    #[inline]
    #[track_caller]
    fn try_from_bytes(reader: impl Read) -> Result<Self, Self::Error> { Self::try_from_bytes_dynamic((), reader) }
}



/// Defines that a type can be parsed from a series of bytes, but requires additional input to do so.
/// 
/// This can be thought of as a configurable counterpart to the [`TryFromBytes`].
/// In fact, the [`TryFromBytes`] is an alias for `TryFromBytesDynamic<()>`.
/// 
/// Typically, you can automatically derive this trait using the [`TryFromBytesDynamic`](crate::procedural::TryFromBytesDynamic)-macro.
/// 
/// # Example
/// ```rust
/// use bytes::TryFromBytesDynamic;
/// 
/// struct Example {
///     num : u16,
/// }
/// impl TryFromBytesDynamic<Option<u16>> for Example {
///     type Error = bytes::errors::ParseError;
/// 
///     #[inline]
///     fn try_from_bytes_dynamic(input: Option<u16>, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
///         if let Some(input) = input {
///             Ok(Self {
///                 num : input,
///             })
///         } else {
///             Ok(Self {
///                 num : u16::try_from_bytes_dynamic((), bytes)?,
///             })
///         }
///     }
/// }
/// 
/// assert_eq!(Example::try_from_bytes_dynamic(Some(42), &[ 0x00, 0x2A ]).unwrap().num, 42);
/// assert_eq!(Example::try_from_bytes_dynamic(None, &[ 0x00, 0x2A ]).unwrap().num, 10752);
/// ```
pub trait TryFromBytesDynamic<I>: Sized {
    /// Determines what errors this trait's functions may throw.
    type Error: Error;


    /// Attempts to parse ourselves from the given input and bytes.
    /// 
    /// # Arguments
    /// - `input`: The additional input needed to make sense of this, like some length.
    /// - `reader`: The [`Read`]er object to parse from.
    /// 
    /// # Returns
    /// A new instance of Self parsed from the given bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to parse the given bytes as ourselves.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, LittleEndian, TryFromBytesDynamic as _};
    /// 
    /// assert_eq!(i16::try_from_bytes_dynamic(BigEndian, &[ 0x00, 0xFF ]).unwrap(), 255);
    /// assert_eq!(i16::try_from_bytes_dynamic(LittleEndian, &[ 0x00, 0xFF ]).unwrap(), -256);
    /// assert_eq!(String::try_from_bytes_dynamic(13, &[ 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ]).unwrap(), "Hello, world!");
    /// ```
    fn try_from_bytes_dynamic(input: I, reader: impl Read) -> Result<Self, Self::Error>;
}

// Implement it for primitives
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<()> for T {
    type Error = crate::errors::ParseError;

    /// Implements the TryFromBytesDynamic parser for primitives using native endianness.
    /// 
    /// # Arguments
    /// - `input`: The input to this parsing (none).
    /// - `reader`: The [`Read`]er to read the bytes to parse from.
    /// 
    /// # Returns
    /// An instance of self that is parsed from the given stream of bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to read the required number of bytes from the given `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(_input: (), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Attempt to read enough information
        // let mut bytes: [ u8; size_of::<T>() ] = [ 0; size_of::<T>() ];
        let mut bytes: [ u8; LENGTH ] = [ 0; LENGTH ];
        if let Err(err) = reader.read_exact(&mut bytes) {
            return Err(ParseError::Read { err });
        }

        // Now simply parse the bytes
        Ok(Self::from_ne_bytes(&bytes))
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<Endianness> for T {
    type Error = crate::errors::ParseError;

    /// Implements the TryFromBytesDynamic parser for primitives using dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines what byte ordering we use to parse.
    /// - `reader`: The [`Read`]er to read the bytes to parse from.
    /// 
    /// # Returns
    /// An instance of self that is parsed from the given stream of bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to read the required number of bytes from the given `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, reader: impl Read) -> Result<Self, Self::Error> {
        // Delegate to the hardcoded implementations
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, reader),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, reader),
        }
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<&Endianness> for T {
    type Error = crate::errors::ParseError;

    /// Implements the TryFromBytesDynamic parser for primitives using dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines what byte ordering we use to parse.
    /// - `reader`: The [`Read`]er to read the bytes to parse from.
    /// 
    /// # Returns
    /// An instance of self that is parsed from the given stream of bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to read the required number of bytes from the given `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &Endianness, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<&mut Endianness> for T {
    type Error = crate::errors::ParseError;

    /// Implements the TryFromBytesDynamic parser for primitives using dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines what byte ordering we use to parse.
    /// - `reader`: The [`Read`]er to read the bytes to parse from.
    /// 
    /// # Returns
    /// An instance of self that is parsed from the given stream of bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to read the required number of bytes from the given `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut Endianness, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<BigEndian> for T {
    type Error = crate::errors::ParseError;

    /// Implements the TryFromBytesDynamic parser for primitives using big-endian ordering.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that decides we're parsing in big-endian byte ordering.
    /// - `reader`: The [`Read`]er to read the bytes to parse from.
    /// 
    /// # Returns
    /// An instance of self that is parsed from the given stream of bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to read the required number of bytes from the given `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(_input: BigEndian, mut reader: impl Read) -> Result<Self, Self::Error> {
        // Attempt to read enough information
        // let mut bytes: [ u8; size_of::<T>() ] = [ 0; size_of::<T>() ];
        let mut bytes: [ u8; LENGTH ] = [ 0; LENGTH ];
        if let Err(err) = reader.read_exact(&mut bytes) {
            return Err(ParseError::Read { err });
        }

        // Now simply parse the bytes
        Ok(Self::from_be_bytes(&bytes))
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<LittleEndian> for T {
    type Error = crate::errors::ParseError;

    /// Implements the TryFromBytesDynamic parser for primitives using little-endian ordering.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that decides we're parsing in little-endian byte ordering.
    /// - `reader`: The [`Read`]er to read the bytes to parse from.
    /// 
    /// # Returns
    /// An instance of self that is parsed from the given stream of bytes.
    /// 
    /// # Errors
    /// This function may error if we failed to read the required number of bytes from the given `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(_input: LittleEndian, mut reader: impl Read) -> Result<Self, Self::Error> {
        // Attempt to read enough information
        // let mut bytes: [ u8; size_of::<T>() ] = [ 0; size_of::<T>() ];
        let mut bytes: [ u8; LENGTH ] = [ 0; LENGTH ];
        if let Err(err) = reader.read_exact(&mut bytes) {
            return Err(ParseError::Read { err });
        }

        // Now simply parse the bytes
        Ok(Self::from_le_bytes(&bytes))
    }
}

// Implement it for tightly-packed containers
impl TryFromBytesDynamic<()> for () {
    type Error = std::convert::Infallible;

    /// Dummy parser that parses nothing.
    /// 
    /// # Arguments
    /// - `input`: Nothing is configurable about this parsing.
    /// - `reader`: A [`Read`]er which we don't touch.
    /// 
    /// # Returns
    /// A new instance of `()`, i.e., nothing.
    /// 
    /// # Errors
    /// This function does not error (hence the return type is [`Infallible`](std::convert::Infallible)).
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(_input: (), _reader: impl Read) -> Result<Self, Self::Error> {
        Ok(())
    }
}
impl TryFromBytesDynamic<usize> for () {
    type Error = crate::errors::ParseError;

    /// Simply moves the reader forward by the given number of bytes but does not parse anything.
    /// 
    /// This can be used to represent reserved or ignored areas in a header.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to skip.
    /// - `reader`: The [`Read`]er to skip bytes in.
    /// 
    /// # Returns
    /// A new instance of `()`, i.e., nothing.
    /// 
    /// # Errors
    /// This function may error if the given reader failed to skip.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: usize, mut reader: impl Read) -> Result<Self, Self::Error> {
        // Attempt to parse & discard
        match reader.read_exact(&mut vec![ 0; input ]) {
            Ok(_)    => Ok(()),
            Err(err) => Err(ParseError::Read { err }),
        }
    }
}
impl<T: TryFromBytesDynamic<I>, I> TryFromBytesDynamic<I> for (T,)
where
    T::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses a tuple wrapped in a tuple with one element.
    /// 
    /// This is useful for... completeness reasons?
    /// 
    /// # Arguments
    /// - `input`: The input to the inner parser.
    /// - `reader`: The reader where the inner parser will gets its bytes from.
    /// 
    /// # Returns
    /// A new instance of the inner type, wrapped in a tuple.
    /// 
    /// # Errors
    /// This function errors whenever the child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: I, reader: impl Read) -> Result<Self, Self::Error> {
        match T::try_from_bytes_dynamic(input, reader) {
            Ok(inner) => Ok((inner,)),
            Err(err)  => Err(ParseError::Field { name: "0".into(), err: Box::new(err) }),
        }
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, I1, I2> TryFromBytesDynamic<(I1, I2)> for (T1, T2)
where
    T1::Error: 'static,
    T2::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses a tuple of nested TryFromBytesDynamic types.
    ///
    /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple of inputs to the inner parsers. These are passed in order, one-to-one.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A tuple with parsed instances of all the inner types.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: (I1, I2), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse the fields one after another
        Ok((
            match T1::try_from_bytes_dynamic(input.0, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "1".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, T3: TryFromBytesDynamic<I3>, I1, I2, I3> TryFromBytesDynamic<(I1, I2, I3)> for (T1, T2, T3)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses a tuple of nested TryFromBytesDynamic types.
    ///
    /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple of inputs to the inner parsers. These are passed in order, one-to-one.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A tuple with parsed instances of all the inner types.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: (I1, I2, I3), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse the fields one after another
        Ok((
            match T1::try_from_bytes_dynamic(input.0, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "2".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, T3: TryFromBytesDynamic<I3>, T4: TryFromBytesDynamic<I4>, I1, I2, I3, I4> TryFromBytesDynamic<(I1, I2, I3, I4)> for (T1, T2, T3, T4)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses a tuple of nested TryFromBytesDynamic types.
    ///
    /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple of inputs to the inner parsers. These are passed in order, one-to-one.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A tuple with parsed instances of all the inner types.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: (I1, I2, I3, I4), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse the fields one after another
        Ok((
            match T1::try_from_bytes_dynamic(input.0, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "3".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, T3: TryFromBytesDynamic<I3>, T4: TryFromBytesDynamic<I4>, T5: TryFromBytesDynamic<I5>, I1, I2, I3, I4, I5> TryFromBytesDynamic<(I1, I2, I3, I4, I5)> for (T1, T2, T3, T4, T5)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses a tuple of nested TryFromBytesDynamic types.
    ///
    /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple of inputs to the inner parsers. These are passed in order, one-to-one.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A tuple with parsed instances of all the inner types.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: (I1, I2, I3, I4, I5), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse the fields one after another
        Ok((
            match T1::try_from_bytes_dynamic(input.0, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "4".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, T3: TryFromBytesDynamic<I3>, T4: TryFromBytesDynamic<I4>, T5: TryFromBytesDynamic<I5>, T6: TryFromBytesDynamic<I6>, I1, I2, I3, I4, I5, I6> TryFromBytesDynamic<(I1, I2, I3, I4, I5, I6)> for (T1, T2, T3, T4, T5, T6)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
    T6::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses a tuple of nested TryFromBytesDynamic types.
    ///
    /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple of inputs to the inner parsers. These are passed in order, one-to-one.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A tuple with parsed instances of all the inner types.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: (I1, I2, I3, I4, I5, I6), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse the fields one after another
        Ok((
            match T1::try_from_bytes_dynamic(input.0, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "4".into(), err: Box::new(err) }); },
            },
            match T6::try_from_bytes_dynamic(input.5, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "5".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, T3: TryFromBytesDynamic<I3>, T4: TryFromBytesDynamic<I4>, T5: TryFromBytesDynamic<I5>, T6: TryFromBytesDynamic<I6>, T7: TryFromBytesDynamic<I7>, I1, I2, I3, I4, I5, I6, I7> TryFromBytesDynamic<(I1, I2, I3, I4, I5, I6, I7)> for (T1, T2, T3, T4, T5, T6, T7)
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

    /// Parses a tuple of nested TryFromBytesDynamic types.
    ///
    /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple of inputs to the inner parsers. These are passed in order, one-to-one.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A tuple with parsed instances of all the inner types.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: (I1, I2, I3, I4, I5, I6, I7), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse the fields one after another
        Ok((
            match T1::try_from_bytes_dynamic(input.0, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "4".into(), err: Box::new(err) }); },
            },
            match T6::try_from_bytes_dynamic(input.5, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "5".into(), err: Box::new(err) }); },
            },
            match T7::try_from_bytes_dynamic(input.6, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "6".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, T3: TryFromBytesDynamic<I3>, T4: TryFromBytesDynamic<I4>, T5: TryFromBytesDynamic<I5>, T6: TryFromBytesDynamic<I6>, T7: TryFromBytesDynamic<I7>, T8: TryFromBytesDynamic<I8>, I1, I2, I3, I4, I5, I6, I7, I8> TryFromBytesDynamic<(I1, I2, I3, I4, I5, I6, I7, I8)> for (T1, T2, T3, T4, T5, T6, T7, T8)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
    T6::Error: 'static,
    T7::Error: 'static,
    T8::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses a tuple of nested TryFromBytesDynamic types.
    ///
    /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple of inputs to the inner parsers. These are passed in order, one-to-one.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A tuple with parsed instances of all the inner types.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: (I1, I2, I3, I4, I5, I6, I7, I8), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse the fields one after another
        Ok((
            match T1::try_from_bytes_dynamic(input.0, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "4".into(), err: Box::new(err) }); },
            },
            match T6::try_from_bytes_dynamic(input.5, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "5".into(), err: Box::new(err) }); },
            },
            match T7::try_from_bytes_dynamic(input.6, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "6".into(), err: Box::new(err) }); },
            },
            match T8::try_from_bytes_dynamic(input.7, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(ParseError::Field { name: "7".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<const LEN: usize, T: for<'a> TryFromBytesDynamic<&'a I>, I: Clone> TryFromBytesDynamic<I> for [ T; LEN ]
where
    for<'a> <T as TryFromBytesDynamic<&'a I>>::Error: 'static,
{
    type Error = crate::errors::ParseError;

    /// Parses an array of a nested TryFromBytesDynamic type.
    ///
    /// This parser assumes the elements are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using a tuple with the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: The input to each of the parsers. It is passed by reference such that the parsers can clone as necessary.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// An array with parsed instances the inner type.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_from_bytes_dynamic(input: I, mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse all of them in-order
        let mut res: [ Option<T>; LEN ] = std::array::from_fn(|_| None);
        for i in 0..LEN {
            res[i] = match T::try_from_bytes_dynamic(&input, &mut reader) {
                Ok(inner) => Some(inner),
                Err(err)  => { return Err(ParseError::Field { name: format!("[{i}]"), err: Box::new(err) }); },
            };
        }
        Ok(res.map(|elem| elem.unwrap()))
    }
}
// impl<T: TryToBytesDynamic<I>, I: Clone> TryToBytesDynamic<I> for [ T ]
// where
//     T::Error: 'static,
// {
//     type Error = crate::errors::SerializeError;

//     fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
//         // Simply serialize all of them in-order
//         for (i, elem) in self.iter().enumerate() {
//             if let Err(err) = elem.try_to_bytes_dynamic(input.clone(), &mut writer) {
//                 return Err(SerializeError::Field { name: format!("[{i}]"), err: Box::new(err) });
//             }
//         }
//         Ok(())
//     }
// }
// impl<T: TryToBytesDynamic<I>, I: Clone> TryToBytesDynamic<I> for Vec<T>
// where
//     T::Error: 'static,
// {
//     type Error = crate::errors::SerializeError;

//     fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
//         // Simply serialize all of them in-order
//         for (i, elem) in self.iter().enumerate() {
//             if let Err(err) = elem.try_to_bytes_dynamic(input.clone(), &mut writer) {
//                 return Err(SerializeError::Field { name: format!("[{i}]"), err: Box::new(err) });
//             }
//         }
//         Ok(())
//     }
// }

// // Implement for string-likes
// impl TryToBytesDynamic<()> for str {
//     type Error = crate::errors::SerializeError;

//     #[inline]
//     fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
//         match writer.write_all(&self.as_bytes()) {
//             Ok(_)    => Ok(()),
//             Err(err) => Err(SerializeError::Writer { err }),
//         }
//     }
// }
// impl TryToBytesDynamic<()> for &str {
//     type Error = crate::errors::SerializeError;

//     #[inline]
//     fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
//         match writer.write_all(&self.as_bytes()) {
//             Ok(_)    => Ok(()),
//             Err(err) => Err(SerializeError::Writer { err }),
//         }
//     }
// }
// impl TryToBytesDynamic<()> for Cow<'_, str> {
//     type Error = crate::errors::SerializeError;

//     #[inline]
//     fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
//         match writer.write_all(&self.as_bytes()) {
//             Ok(_)    => Ok(()),
//             Err(err) => Err(SerializeError::Writer { err }),
//         }
//     }
// }
// impl TryToBytesDynamic<()> for String {
//     type Error = crate::errors::SerializeError;

//     #[inline]
//     fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
//         match writer.write_all(&self.as_bytes()) {
//             Ok(_)    => Ok(()),
//             Err(err) => Err(SerializeError::Writer { err }),
//         }
//     }
// }

// // Implement it for primitives
// impl TryFromBytesDynamic<()> for u8 {
//     type Error = crate::errors::ParseError;

//     /// Parses the byte as-is from the input stream.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is empty.
//     #[inline]
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let bytes: &[u8] = bytes.as_ref();
//         if !bytes.is_empty() {
//             Ok(bytes[0])
//         } else {
//             Err(ParseError::NotEnoughInput { got: 0, needed: 1 })
//         }
//     }
// }
// impl TryFromBytesDynamic<()> for i8 {
//     type Error = crate::errors::ParseError;

//     /// Parses the byte as a signed integer from the input stream.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is empty.
//     #[inline]
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let bytes: &[u8] = bytes.as_ref();
//         if !bytes.is_empty() {
//             Ok(bytes[0] as i8)
//         } else {
//             Err(ParseError::NotEnoughInput { got: 0, needed: 1 })
//         }
//     }
// }
// impl TryFromBytesDynamic<()> for u16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, unsigned integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for u16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, unsigned integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for u16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, unsigned integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for u16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, unsigned integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for i16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, signed integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for i16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, signed integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for i16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, signed integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for i16 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 16-bit, signed integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than two bytes in it.
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for u32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, unsigned integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for u32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, unsigned integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for u32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, unsigned integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for u32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, unsigned integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for i32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, signed integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for i32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, signed integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for i32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, signed integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for i32 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 32-bit, signed integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than four bytes in it.
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for u64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, unsigned integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for u64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, unsigned integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for u64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, unsigned integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for u64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, unsigned integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for i64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, signed integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for i64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, signed integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for i64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, signed integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for i64 {
//     type Error = crate::errors::ParseError;

//     /// Parses a 64-bit, signed integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice has less than eight bytes in it.
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for usize {
//     type Error = crate::errors::ParseError;

//     /// Parses an unsigned integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`usize`].
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for usize {
//     type Error = crate::errors::ParseError;

//     /// Parses an unsigned integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`usize`].
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for usize {
//     type Error = crate::errors::ParseError;

//     /// Parses an unsigned integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`usize`].
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for usize {
//     type Error = crate::errors::ParseError;

//     /// Parses an unsigned integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`usize`].
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for isize {
//     type Error = crate::errors::ParseError;

//     /// Parses a signed integer from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent an [`isize`].
//     fn try_from_bytes_dynamic(_input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_ne_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<Endianness> for isize {
//     type Error = crate::errors::ParseError;

//     /// Parses a signed integer from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`isize`].
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for isize {
//     type Error = crate::errors::ParseError;

//     /// Parses a signed integer from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent an [`isize`].
//     fn try_from_bytes_dynamic(_input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_be_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for isize {
//     type Error = crate::errors::ParseError;

//     /// Parses an unsigned integer from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent an [`isize`].
//     fn try_from_bytes_dynamic(_input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();

//         // Assert the length checks out
//         if bytes.len() > size_of::<Self>() { bytes = &bytes[..size_of::<Self>()]; }
//         else if bytes.len() < size_of::<Self>() { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: size_of::<Self>() }) }
//         Ok(Self::from_le_bytes(bytes.try_into().unwrap()))
//     }
// }
// impl TryFromBytesDynamic<()> for char {
//     type Error = crate::errors::ParseError;

//     /// Parses a unicode character from the input stream.
//     /// 
//     /// Note that this function uses native endianness. For a static endianness, consider using [`TryFromBytesDynamic<Endianness>`], [`TryFromBytesDynamic<BigEndian>`] or [`TryFromBytesDynamic<LittleEndian>`].
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`char`].
//     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         // Parse the input as a u32 first
//         let raw: u32 = u32::try_from_bytes_dynamic(input, bytes)?;
//         match Self::from_u32(raw) {
//             Some(val) => Ok(val),
//             None      => Err(ParseError::NonUtf8Char { raw }),
//         }
//     }
// }
// impl TryFromBytesDynamic<Endianness> for char {
//     type Error = crate::errors::ParseError;

//     /// Parses a unicode character from the input stream using dynamic endianness.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`char`].
//     #[inline]
//     fn try_from_bytes_dynamic(input: Endianness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, bytes),
//             Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, bytes),
//         }
//     }
// }
// impl TryFromBytesDynamic<BigEndian> for char {
//     type Error = crate::errors::ParseError;

//     /// Parses a unicode character from the input stream using big-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`char`].
//     fn try_from_bytes_dynamic(input: BigEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         // Parse the input as a u32 first
//         let raw: u32 = u32::try_from_bytes_dynamic(input, bytes)?;
//         match Self::from_u32(raw) {
//             Some(val) => Ok(val),
//             None      => Err(ParseError::NonUtf8Char { raw }),
//         }
//     }
// }
// impl TryFromBytesDynamic<LittleEndian> for char {
//     type Error = crate::errors::ParseError;

//     /// Parses a unicode character from the input stream using little-endian ordering.
//     /// 
//     /// # Errors
//     /// This function may error if the given slice is too small to represent a [`char`].
//     fn try_from_bytes_dynamic(input: LittleEndian, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         // Parse the input as a u32 first
//         let raw: u32 = u32::try_from_bytes_dynamic(input, bytes)?;
//         match Self::from_u32(raw) {
//             Some(val) => Ok(val),
//             None      => Err(ParseError::NonUtf8Char { raw }),
//         }
//     }
// }

// // Implement for tightly-packed containers
// impl<I> TryFromBytesDynamic<I> for () {
//     type Error = std::convert::Infallible;

//     /// A dummy parser that parses nothing.
//     /// 
//     /// This parser may be used to represent unused areas in a tightly packed struct. See below for an example.
//     /// 
//     /// # Arguments
//     /// - `input`: The input to customize the parsing. Note that this is actually ignored because we're not parsing anything.
//     /// - `bytes`: The byte string to parse from. Note that this is actually ignored because we're not parsing anything.
//     /// 
//     /// # Returns
//     /// A new instance of `()`.
//     /// 
//     /// # Examples
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<()>::try_from_bytes(&[ 0x2A ]).unwrap(), ());
//     /// ```
//     /// Example usage in a tightly packed struct:
//     /// ```rust
//     /// use bytes::TryFromBytes;
//     /// 
//     /// #[derive(TryFromBytes)]
//     /// struct PackedWithUnused {
//     ///     /// First part
//     ///     #[bytes]
//     ///     num1   : u16,
//     ///     /// Unused area of 2 bytes
//     ///     #[bytes(length = 2)]
//     ///     unused : (),
//     ///     /// Second part
//     ///     #[bytes]
//     ///     num2   : u16,
//     /// }
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(_input: I, _bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> { Ok(()) }
// }
// impl<T: TryFromBytesDynamic<I>, I> TryFromBytesDynamic<I> for (T,)
// where
//     T::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a particular type wrapped in a tuple.
//     /// 
//     /// # Arguments
//     /// - `input`: Any input to pass to the child parser.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with one element that is parsed with the nested parser.
//     /// 
//     /// # Errors
//     /// This function errors if the child parser errors. If so, the error is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<(u8,)>::try_from_bytes(&[ 0x2A ]).unwrap(), (42,));
//     /// ```
//     fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         Ok((
//             T::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<()>, T2: TryFromBytesDynamic<()>> TryFromBytesDynamic<()> for (T1, T2)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: Nothing, since this parser assumes the nested types do not need input either.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<(u8, u8)>::try_from_bytes(&[ 0x2A, 0x2B ]).unwrap(), (42, 43));
//     /// ```
//     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, I1, I2> TryFromBytesDynamic<(I1, I2)> for (T1, T2)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: A tuple with inputs to pass to each of the nested parsers.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(<(String, String)>::try_from_bytes_dynamic((2, 2), &[ 0x61, 0x62, 0x63, 0x64 ]).unwrap(), ("ab".into(), "cd".into()));
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: (I1, I2), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input.0, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input.1, bytes).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<()>, T2: ParsedLength + TryFromBytesDynamic<()>, T3: TryFromBytesDynamic<()>> TryFromBytesDynamic<()> for (T1, T2, T3)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: Nothing, since this parser assumes the nested types do not need input either.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<(u8, u8, u8)>::try_from_bytes(&[ 0x2A, 0x2B, 0x2C ]).unwrap(), (42, 43, 44));
//     /// ```
//     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<I1>, T2: ParsedLength + TryFromBytesDynamic<I2>, T3: TryFromBytesDynamic<I3>, I1, I2, I3> TryFromBytesDynamic<(I1, I2, I3)> for (T1, T2, T3)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: A tuple with inputs to pass to each of the nested parsers.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(<(String, String, String)>::try_from_bytes_dynamic((2, 2, 2), &[ 0x61, 0x62, 0x63, 0x64, 0x65, 0x66 ]).unwrap(), ("ab".into(), "cd".into(), "ef".into()));
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: (I1, I2, I3), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input.0, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input.1, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input.2, bytes).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<()>, T2: ParsedLength + TryFromBytesDynamic<()>, T3: ParsedLength + TryFromBytesDynamic<()>, T4: TryFromBytesDynamic<()>> TryFromBytesDynamic<()> for (T1, T2, T3, T4)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: Nothing, since this parser assumes the nested types do not need input either.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<(u8, u8, u8, u8)>::try_from_bytes(&[ 0x2A, 0x2B, 0x2C, 0x2D ]).unwrap(), (42, 43, 44, 45));
//     /// ```
//     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<I1>, T2: ParsedLength + TryFromBytesDynamic<I2>, T3: ParsedLength + TryFromBytesDynamic<I3>, T4: TryFromBytesDynamic<I4>, I1, I2, I3, I4> TryFromBytesDynamic<(I1, I2, I3, I4)> for (T1, T2, T3, T4)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: A tuple with inputs to pass to each of the nested parsers.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(<(String, String, String, String)>::try_from_bytes_dynamic((2, 2, 2, 2), &[ 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68 ]).unwrap(), ("ab".into(), "cd".into(), "ef".into(), "gh".into()));
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: (I1, I2, I3, I4), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input.0, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input.1, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input.2, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input.3, bytes).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<()>, T2: ParsedLength + TryFromBytesDynamic<()>, T3: ParsedLength + TryFromBytesDynamic<()>, T4: ParsedLength + TryFromBytesDynamic<()>, T5: TryFromBytesDynamic<()>> TryFromBytesDynamic<()> for (T1, T2, T3, T4, T5)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
//     T5::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: Nothing, since this parser assumes the nested types do not need input either.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<(u8, u8, u8, u8, u8)>::try_from_bytes(&[ 0x2A, 0x2B, 0x2C, 0x2D, 0x2E ]).unwrap(), (42, 43, 44, 45, 46));
//     /// ```
//     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//             T5::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<I1>, T2: ParsedLength + TryFromBytesDynamic<I2>, T3: ParsedLength + TryFromBytesDynamic<I3>, T4: ParsedLength + TryFromBytesDynamic<I4>, T5: TryFromBytesDynamic<I5>, I1, I2, I3, I4, I5> TryFromBytesDynamic<(I1, I2, I3, I4, I5)> for (T1, T2, T3, T4, T5)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
//     T5::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: A tuple with inputs to pass to each of the nested parsers.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(<(String, String, String, String, String)>::try_from_bytes_dynamic((2, 2, 2, 2, 2), &[ 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A ]).unwrap(), ("ab".into(), "cd".into(), "ef".into(), "gh".into(), "ij".into()));
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: (I1, I2, I3, I4, I5), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input.0, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input.1, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input.2, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input.3, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//             T5::try_from_bytes_dynamic(input.4, bytes).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<()>, T2: ParsedLength + TryFromBytesDynamic<()>, T3: ParsedLength + TryFromBytesDynamic<()>, T4: ParsedLength + TryFromBytesDynamic<()>, T5: ParsedLength + TryFromBytesDynamic<()>, T6: TryFromBytesDynamic<()>> TryFromBytesDynamic<()> for (T1, T2, T3, T4, T5, T6)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
//     T5::Error: 'static,
//     T6::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: Nothing, since this parser assumes the nested types do not need input either.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<(u8, u8, u8, u8, u8, u8)>::try_from_bytes(&[ 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F ]).unwrap(), (42, 43, 44, 45, 46 ,47));
//     /// ```
//     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//             T5::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
//             T6::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "5".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<I1>, T2: ParsedLength + TryFromBytesDynamic<I2>, T3: ParsedLength + TryFromBytesDynamic<I3>, T4: ParsedLength + TryFromBytesDynamic<I4>, T5: ParsedLength + TryFromBytesDynamic<I5>, T6: TryFromBytesDynamic<I6>, I1, I2, I3, I4, I5, I6> TryFromBytesDynamic<(I1, I2, I3, I4, I5, I6)> for (T1, T2, T3, T4, T5, T6)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
//     T5::Error: 'static,
//     T6::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: A tuple with inputs to pass to each of the nested parsers.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(<(String, String, String, String, String, String)>::try_from_bytes_dynamic((2, 2, 2, 2, 2, 2), &[ 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C ]).unwrap(), ("ab".into(), "cd".into(), "ef".into(), "gh".into(), "ij".into(), "kl".into()));
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: (I1, I2, I3, I4, I5, I6), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input.0, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input.1, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input.2, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input.3, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//             T5::try_from_bytes_dynamic(input.4, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
//             T6::try_from_bytes_dynamic(input.5, bytes).map_err(|err| ParseError::Field { name: "5".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<()>, T2: ParsedLength + TryFromBytesDynamic<()>, T3: ParsedLength + TryFromBytesDynamic<()>, T4: ParsedLength + TryFromBytesDynamic<()>, T5: ParsedLength + TryFromBytesDynamic<()>, T6: ParsedLength + TryFromBytesDynamic<()>, T7: TryFromBytesDynamic<()>> TryFromBytesDynamic<()> for (T1, T2, T3, T4, T5, T6, T7)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
//     T5::Error: 'static,
//     T6::Error: 'static,
//     T7::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: Nothing, since this parser assumes the nested types do not need input either.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<(u8, u8, u8, u8, u8, u8)>::try_from_bytes(&[ 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F ]).unwrap(), (42, 43, 44, 45, 46 ,47));
//     /// ```
//     fn try_from_bytes_dynamic(input: (), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//             T5::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
//             T6::try_from_bytes_dynamic(input, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "5".into(), err: Box::new(err) })?,
//             T7::try_from_bytes_dynamic(input, bytes).map_err(|err| ParseError::Field { name: "6".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<T1: ParsedLength + TryFromBytesDynamic<I1>, T2: ParsedLength + TryFromBytesDynamic<I2>, T3: ParsedLength + TryFromBytesDynamic<I3>, T4: ParsedLength + TryFromBytesDynamic<I4>, T5: ParsedLength + TryFromBytesDynamic<I5>, T6: ParsedLength + TryFromBytesDynamic<I6>, T7: TryFromBytesDynamic<I7>, I1, I2, I3, I4, I5, I6, I7> TryFromBytesDynamic<(I1, I2, I3, I4, I5, I6, I7)> for (T1, T2, T3, T4, T5, T6, T7)
// where
//     T1::Error: 'static,
//     T2::Error: 'static,
//     T3::Error: 'static,
//     T4::Error: 'static,
//     T5::Error: 'static,
//     T6::Error: 'static,
//     T7::Error: 'static,
// {
//     type Error = crate::errors::ParseError;

//     /// Parses a tuple of nested types.
//     /// 
//     /// The tuple is assumed to be tightly packed; i.e., first the first type is parsed, and then immediately after the next is parsed, etc.
//     /// 
//     /// The length of skips are deduced on each non-last type's [`ParsedLength`]-implementation.
//     /// 
//     /// # Arguments
//     /// - `input`: A tuple with inputs to pass to each of the nested parsers.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new tuple with elements, each parsed with the appropriate nested parser.
//     /// 
//     /// # Errors
//     /// This function errors (eagerly) if any of the nested parsers fails. If so, then the errors is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(<(String, String, String, String, String, String)>::try_from_bytes_dynamic((2, 2, 2, 2, 2, 2), &[ 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C ]).unwrap(), ("ab".into(), "cd".into(), "ef".into(), "gh".into(), "ij".into(), "kl".into()));
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: (I1, I2, I3, I4, I5, I6, I7), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let mut bytes: &[u8] = bytes.as_ref();
//         Ok((
//             T1::try_from_bytes_dynamic(input.0, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "0".into(), err: Box::new(err) })?,
//             T2::try_from_bytes_dynamic(input.1, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "1".into(), err: Box::new(err) })?,
//             T3::try_from_bytes_dynamic(input.2, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "2".into(), err: Box::new(err) })?,
//             T4::try_from_bytes_dynamic(input.3, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "3".into(), err: Box::new(err) })?,
//             T5::try_from_bytes_dynamic(input.4, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "4".into(), err: Box::new(err) })?,
//             T6::try_from_bytes_dynamic(input.5, bytes).map(|val| { bytes = &bytes[val.parsed_len()..]; val }).map_err(|err| ParseError::Field { name: "5".into(), err: Box::new(err) })?,
//             T7::try_from_bytes_dynamic(input.6, bytes).map_err(|err| ParseError::Field { name: "6".into(), err: Box::new(err) })?,
//         ))
//     }
// }
// impl<const LEN: usize, T: ParsedLength + TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<I> for [ T; LEN ]
// where
//     T::Error: 'static,
// {
//     type Error = ParseError;

//     /// Parses a (constant-length) array of a nested type.
//     /// 
//     /// The items are assumed to be tightly packed, shortly following after another.
//     /// 
//     /// # Arguments
//     /// - `input`: Any input to pass to the child parsers.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new array with elements, each parsed with the nested parser.
//     /// 
//     /// # Errors
//     /// This function may error if any of the elements fails to be parsed. If so, then the error is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytes as _;
//     /// 
//     /// assert_eq!(<[ u8; 4 ]>::try_from_bytes(&[ 0x2A, 0x2B, 0x2C, 0x2D ]).unwrap(), [ 42, 43, 44, 45 ]);
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: I, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         // Parse them all, Pokémon
//         let mut bytes: &[u8] = bytes.as_ref();
//         let mut res: [ Option<T>; LEN ] = std::array::from_fn(|_| None);
//         for (i, e) in res.iter_mut().enumerate() {
//             // Parse the element
//             let val: T = match T::try_from_bytes_dynamic(input.clone(), bytes) {
//                 Ok(val)  => val,
//                 Err(err) => { return Err(ParseError::Field { name: format!("[{i}]"), err: Box::new(err) }); },
//             };

//             // Update the offset, then continue
//             bytes = &bytes[val.parsed_len()..];
//             *e = Some(val);
//         }

//         // Alright, return the mapped version
//         Ok(res.map(|e| e.unwrap()))
//     }
// }
// impl<T: ParsedLength + TryFromBytesDynamic<I>, I: Clone> TryFromBytesDynamic<(usize, I)> for Vec<T>
// where
//     T::Error: 'static,
// {
//     type Error = ParseError;

//     /// Parses a dynamic number of elements of a nested type.
//     /// 
//     /// The array is assumed to be tightly-packed.
//     /// 
//     /// # Arguments
//     /// - `input`: A tuple with first the number of times to apply the parser, and then an additional input for every nested parser.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// A new vector with elements, each parsed with the nested parser.
//     /// 
//     /// # Errors
//     /// This function errors if any of the parsers fail. If so, then the error is wrapped in a [`ParseError::Field`].
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(Vec::<u8>::try_from_bytes_dynamic((4, ()), &[ 0x2A, 0x2B, 0x2C, 0x2D ]).unwrap(), vec![ 42, 43, 44, 45 ]);
//     /// ```
//     fn try_from_bytes_dynamic(input: (usize, I), bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         // Construct the list
//         let mut bytes: &[u8] = bytes.as_ref();
//         let mut res: Vec<T> = Vec::with_capacity(input.0);
//         for i in 0..input.0 {
//             // Parse the element
//             let val: T = match T::try_from_bytes_dynamic(input.1.clone(), bytes) {
//                 Ok(val)  => val,
//                 Err(err) => { return Err(ParseError::Field { name: format!("[{i}]"), err: Box::new(err) }); },
//             };

//             // Update the offset, then continue
//             bytes = &bytes[val.parsed_len()..];
//             res.push(val);
//         }

//         // Done, return the vector
//         Ok(res)
//     }
// }

// // Implement for string-like
// impl TryFromBytesDynamic<usize> for Cow<'_, str> {
//     type Error = ParseError;

//     /// Parses a string as a [`Cow<str>`].
//     /// 
//     /// Note that the value is always returned by ownership, not reference.
//     /// 
//     /// # Arguments
//     /// - `input`: Determines the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`Cow<str>`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes, or if it wasn't valid UTF-8.
//     /// 
//     /// # Example
//     /// ```rust
//     /// # use std::borrow::Cow;
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(Cow::<str>::try_from_bytes_dynamic(3, &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert!(Cow::<str>::try_from_bytes_dynamic(3, &[ 0xFF, 0x6F, 0x6F ]).is_err());
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: usize, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         Self::try_from_bytes_dynamic(NonLossy(input), bytes)
//     }
// }
// impl TryFromBytesDynamic<Lossiness> for Cow<'_, str> {
//     type Error = ParseError;

//     /// Parses a string as a [`Cow<str>`].
//     /// 
//     /// Note that the value is always returned by ownership, not reference.
//     /// 
//     /// # Arguments
//     /// - `input`: Determines if we're parsing lossy or lossless _and_ the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`Cow<str>`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes, or if it we were parsing lossless and the input wasn't valid UTF-8.
//     /// 
//     /// # Example
//     /// ```rust
//     /// # use std::borrow::Cow;
//     /// use bytes::{Lossiness, TryFromBytesDynamic as _};
//     /// 
//     /// assert_eq!(Cow::<str>::try_from_bytes_dynamic(Lossiness::Lossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert_eq!(Cow::<str>::try_from_bytes_dynamic(Lossiness::NonLossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert_eq!(Cow::<str>::try_from_bytes_dynamic(Lossiness::Lossy(3), &[ 0xFF, 0x6F, 0x6F ]).unwrap(), "�oo");
//     /// assert!(Cow::<str>::try_from_bytes_dynamic(Lossiness::NonLossy(3), &[ 0xFF, 0x6F, 0x6F ]).is_err());
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: Lossiness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Lossiness::Lossy(l)    => Self::try_from_bytes_dynamic(Lossy(l), bytes),
//             Lossiness::NonLossy(n) => Self::try_from_bytes_dynamic(NonLossy(n), bytes),
//         }        
//     }
// }
// impl TryFromBytesDynamic<Lossy> for Cow<'_, str> {
//     type Error = ParseError;

//     /// Parses a string as a [`Cow<str>`].
//     /// 
//     /// Note that this function parses lossy, i.e., non-UTF-8 characters are replaced by a special 'unknown' character (`�`).
//     /// 
//     /// Also note that the value is always returned by ownership, not reference.
//     /// 
//     /// # Arguments
//     /// - `input`: Determines that we're parsing lossy _and_ the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`Cow<str>`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes.
//     /// 
//     /// # Example
//     /// ```rust
//     /// # use std::borrow::Cow;
//     /// use bytes::{Lossy, TryFromBytesDynamic as _};
//     /// 
//     /// assert_eq!(Cow::<str>::try_from_bytes_dynamic(Lossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert_eq!(Cow::<str>::try_from_bytes_dynamic(Lossy(3), &[ 0xFF, 0x6F, 0x6F ]).unwrap(), "�oo");
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: Lossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let bytes: &[u8] = bytes.as_ref();

//         // Attempt to take a large enough slice
//         if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
//         let bytes: &[u8] = &bytes[..input.0];

//         // Next, attempt to convert it to a string
//         Ok(Cow::Owned(String::from_utf8_lossy(bytes).to_string()))
//     }
// }
// impl TryFromBytesDynamic<NonLossy> for Cow<'_, str> {
//     type Error = ParseError;

//     /// Parses a string as a [`Cow<str>`].
//     /// 
//     /// Note that this function parses lossless, i.e., the parsing crashes when it finds non-UTF-8 characters.
//     /// 
//     /// Also note that the value is always returned by ownership, not reference.
//     /// 
//     /// # Arguments
//     /// - `input`: Determines that we're parsing lossless _and_ the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`Cow<str>`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes, or if the input wasn't valid UTF-8.
//     /// 
//     /// # Example
//     /// ```rust
//     /// # use std::borrow::Cow;
//     /// use bytes::{NonLossy, TryFromBytesDynamic as _};
//     /// 
//     /// assert_eq!(Cow::<str>::try_from_bytes_dynamic(NonLossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert!(Cow::<str>::try_from_bytes_dynamic(NonLossy(3), &[ 0xFF, 0x6F, 0x6F ]).is_err());
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: NonLossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let bytes: &[u8] = bytes.as_ref();

//         // Attempt to take a large enough slice
//         if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
//         let bytes: &[u8] = &bytes[..input.0];

//         // Next, attempt to convert it to a string
//         match String::from_utf8(bytes.into()) {
//             Ok(val)  => Ok(Cow::Owned(val)),
//             Err(err) => Err(ParseError::NonUtf8String { err }),
//         }
//     }
// }
// impl TryFromBytesDynamic<usize> for String {
//     type Error = ParseError;

//     /// Parses a string as a [`String`].
//     /// 
//     /// # Arguments
//     /// - `input`: Determines the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`String`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes, or if it wasn't valid UTF-8.
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::TryFromBytesDynamic as _;
//     /// 
//     /// assert_eq!(String::try_from_bytes_dynamic(3, &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert!(String::try_from_bytes_dynamic(3, &[ 0xFF, 0x6F, 0x6F ]).is_err());
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: usize, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         Self::try_from_bytes_dynamic(NonLossy(input), bytes)
//     }
// }
// impl TryFromBytesDynamic<Lossiness> for String {
//     type Error = ParseError;

//     /// Parses a string as a [`String`].
//     /// 
//     /// # Arguments
//     /// - `input`: Determines if we're parsing lossy or lossless _and_ the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`String`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes, or if it we were parsing lossless and the input wasn't valid UTF-8.
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::{Lossiness, TryFromBytesDynamic as _};
//     /// 
//     /// assert_eq!(String::try_from_bytes_dynamic(Lossiness::Lossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert_eq!(String::try_from_bytes_dynamic(Lossiness::NonLossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert_eq!(String::try_from_bytes_dynamic(Lossiness::Lossy(3), &[ 0xFF, 0x6F, 0x6F ]).unwrap(), "�oo");
//     /// assert!(String::try_from_bytes_dynamic(Lossiness::NonLossy(3), &[ 0xFF, 0x6F, 0x6F ]).is_err());
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: Lossiness, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         match input {
//             Lossiness::Lossy(l)    => Self::try_from_bytes_dynamic(Lossy(l), bytes),
//             Lossiness::NonLossy(n) => Self::try_from_bytes_dynamic(NonLossy(n), bytes),
//         }        
//     }
// }
// impl TryFromBytesDynamic<Lossy> for String {
//     type Error = ParseError;

//     /// Parses a string as a [`String`].
//     /// 
//     /// Note that this function parses lossy, i.e., non-UTF-8 characters are replaced by a special 'unknown' character (`�`).
//     /// 
//     /// # Arguments
//     /// - `input`: Determines that we're parsing lossy _and_ the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`String`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes.
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::{Lossy, TryFromBytesDynamic as _};
//     /// 
//     /// assert_eq!(String::try_from_bytes_dynamic(Lossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert_eq!(String::try_from_bytes_dynamic(Lossy(3), &[ 0xFF, 0x6F, 0x6F ]).unwrap(), "�oo");
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: Lossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let bytes: &[u8] = bytes.as_ref();

//         // Attempt to take a large enough slice
//         if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
//         let bytes: &[u8] = &bytes[..input.0];

//         // Next, attempt to convert it to a string
//         Ok(String::from_utf8_lossy(bytes).into_owned())
//     }
// }
// impl TryFromBytesDynamic<NonLossy> for String {
//     type Error = ParseError;

//     /// Parses a string as a [`String`].
//     /// 
//     /// Note that this function parses lossless, i.e., the parsing crashes when it finds non-UTF-8 characters.
//     /// 
//     /// # Arguments
//     /// - `input`: Determines that we're parsing lossless _and_ the length of the input to parse. Note that this length is in _bytes_, not in characters.
//     /// - `bytes`: The byte string to parse from.
//     /// 
//     /// # Returns
//     /// The parsed string as a [`String`].
//     /// 
//     /// # Errors
//     /// This function may error if the input was not at least `input` bytes, or if the input wasn't valid UTF-8.
//     /// 
//     /// # Example
//     /// ```rust
//     /// use bytes::{NonLossy, TryFromBytesDynamic as _};
//     /// 
//     /// assert_eq!(String::try_from_bytes_dynamic(NonLossy(3), &[ 0x66, 0x6F, 0x6F ]).unwrap(), "foo");
//     /// assert!(String::try_from_bytes_dynamic(NonLossy(3), &[ 0xFF, 0x6F, 0x6F ]).is_err());
//     /// ```
//     #[inline]
//     fn try_from_bytes_dynamic(input: NonLossy, bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
//         let bytes: &[u8] = bytes.as_ref();

//         // Attempt to take a large enough slice
//         if bytes.len() < input.0 { return Err(ParseError::NotEnoughInput { got: bytes.len(), needed: input.0 }); }
//         let bytes: &[u8] = &bytes[..input.0];

//         // Next, attempt to convert it to a string
//         match String::from_utf8(bytes.into()) {
//             Ok(val)  => Ok(val),
//             Err(err) => Err(ParseError::NonUtf8String { err }),
//         }
//     }
// }



/// Allows a type to be serialized to bytes, using some additional input for configuration.
/// 
/// This can be automatically derived using the [`ToBytesDynamic`](crate::procedural::ToBytesDynamic)-macro.
/// 
/// # Example
/// ```rust
/// todo!();
/// ```
pub trait TryToBytesDynamic<I> {
    /// The type of error that may occur when serializing.
    type Error: Error;


    /// Attempts to serialize ourselves to a stream of bytes using dynamic input for configuration.
    /// 
    /// # Arguments
    /// - `input`: The additional input needed to make sense of this, like some length.
    /// - `writer`: The [output stream](std::io::Write) to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the given bytes.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_to_bytes_dynamic(&self, input: I, writer: impl Write) -> Result<(), Self::Error>;
}

// Implement it for primitives
impl<T: PrimitiveToBytes> TryToBytesDynamic<()> for T {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply call the trait thingy
        match writer.write_all(self.to_ne_bytes().as_ref()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<Endianness> for T {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: Endianness, writer: impl Write) -> Result<(), Self::Error> {
        // Delegate to the hardcoded implementations
        match input {
            Endianness::Big    => self.try_to_bytes_dynamic(BigEndian, writer),
            Endianness::Little => self.try_to_bytes_dynamic(LittleEndian, writer),
        }
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<BigEndian> for T {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: BigEndian, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply call the trait thingy
        match writer.write_all(self.to_be_bytes().as_ref()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<LittleEndian> for T {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: LittleEndian, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply call the trait thingy
        match writer.write_all(self.to_le_bytes().as_ref()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}

// Implement it for tightly-packed containers
impl TryToBytesDynamic<()> for () {
    type Error = std::convert::Infallible;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), _writer: impl Write) -> Result<(), Self::Error> {
        Ok(())
    }
}
impl TryToBytesDynamic<usize> for () {
    type Error = crate::errors::SerializeError;

    /// This functions writes the given number of zeroes to the given writer.
    /// 
    /// This is useful for writing headers with reserved or ignored areas.
    /// 
    /// # Arguments
    /// - `input`: The number of zero-bytes to write.
    /// - `writer`: The [`Write`]er to write to.
    /// 
    /// # Errors
    /// This function errors if we failed to write to the given writer.
    #[inline]
    fn try_to_bytes_dynamic(&self, input: usize, mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&vec![ 0; input ]) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}
impl<T: TryToBytesDynamic<I>, I> TryToBytesDynamic<I> for (T,)
where
    T::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: I, writer: impl Write) -> Result<(), Self::Error> {
        match self.0.try_to_bytes_dynamic(input, writer) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Field { name: "0".into(), err: Box::new(err) }),
        }
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, I1, I2> TryToBytesDynamic<(I1, I2)> for (T1, T2)
where
    T1::Error: 'static,
    T2::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(SerializeError::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, writer) {
            return Err(SerializeError::Field { name: "1".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, T3: TryToBytesDynamic<I3>, I1, I2, I3> TryToBytesDynamic<(I1, I2, I3)> for (T1, T2, T3)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(SerializeError::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(SerializeError::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, writer) {
            return Err(SerializeError::Field { name: "2".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, T3: TryToBytesDynamic<I3>, T4: TryToBytesDynamic<I4>, I1, I2, I3, I4> TryToBytesDynamic<(I1, I2, I3, I4)> for (T1, T2, T3, T4)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(SerializeError::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(SerializeError::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(SerializeError::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, writer) {
            return Err(SerializeError::Field { name: "3".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, T3: TryToBytesDynamic<I3>, T4: TryToBytesDynamic<I4>, T5: TryToBytesDynamic<I5>, I1, I2, I3, I4, I5> TryToBytesDynamic<(I1, I2, I3, I4, I5)> for (T1, T2, T3, T4, T5)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(SerializeError::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(SerializeError::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(SerializeError::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(SerializeError::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, writer) {
            return Err(SerializeError::Field { name: "4".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, T3: TryToBytesDynamic<I3>, T4: TryToBytesDynamic<I4>, T5: TryToBytesDynamic<I5>, T6: TryToBytesDynamic<I6>, I1, I2, I3, I4, I5, I6> TryToBytesDynamic<(I1, I2, I3, I4, I5, I6)> for (T1, T2, T3, T4, T5, T6)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
    T6::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5, I6), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(SerializeError::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(SerializeError::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(SerializeError::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(SerializeError::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, &mut writer) {
            return Err(SerializeError::Field { name: "4".into(), err: Box::new(err) });
        }
        if let Err(err) = self.5.try_to_bytes_dynamic(input.5, writer) {
            return Err(SerializeError::Field { name: "5".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, T3: TryToBytesDynamic<I3>, T4: TryToBytesDynamic<I4>, T5: TryToBytesDynamic<I5>, T6: TryToBytesDynamic<I6>, T7: TryToBytesDynamic<I7>, I1, I2, I3, I4, I5, I6, I7> TryToBytesDynamic<(I1, I2, I3, I4, I5, I6, I7)> for (T1, T2, T3, T4, T5, T6, T7)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
    T6::Error: 'static,
    T7::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5, I6, I7), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(SerializeError::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(SerializeError::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(SerializeError::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(SerializeError::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, &mut writer) {
            return Err(SerializeError::Field { name: "4".into(), err: Box::new(err) });
        }
        if let Err(err) = self.5.try_to_bytes_dynamic(input.5, &mut writer) {
            return Err(SerializeError::Field { name: "5".into(), err: Box::new(err) });
        }
        if let Err(err) = self.6.try_to_bytes_dynamic(input.6, writer) {
            return Err(SerializeError::Field { name: "6".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, T3: TryToBytesDynamic<I3>, T4: TryToBytesDynamic<I4>, T5: TryToBytesDynamic<I5>, T6: TryToBytesDynamic<I6>, T7: TryToBytesDynamic<I7>, T8: TryToBytesDynamic<I8>, I1, I2, I3, I4, I5, I6, I7, I8> TryToBytesDynamic<(I1, I2, I3, I4, I5, I6, I7, I8)> for (T1, T2, T3, T4, T5, T6, T7, T8)
where
    T1::Error: 'static,
    T2::Error: 'static,
    T3::Error: 'static,
    T4::Error: 'static,
    T5::Error: 'static,
    T6::Error: 'static,
    T7::Error: 'static,
    T8::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5, I6, I7, I8), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(SerializeError::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(SerializeError::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(SerializeError::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(SerializeError::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, &mut writer) {
            return Err(SerializeError::Field { name: "4".into(), err: Box::new(err) });
        }
        if let Err(err) = self.5.try_to_bytes_dynamic(input.5, &mut writer) {
            return Err(SerializeError::Field { name: "5".into(), err: Box::new(err) });
        }
        if let Err(err) = self.6.try_to_bytes_dynamic(input.6, &mut writer) {
            return Err(SerializeError::Field { name: "6".into(), err: Box::new(err) });
        }
        if let Err(err) = self.7.try_to_bytes_dynamic(input.7, writer) {
            return Err(SerializeError::Field { name: "7".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<const LEN: usize, T: TryToBytesDynamic<I>, I: Clone> TryToBytesDynamic<I> for [ T; LEN ]
where
    T::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize all of them in-order
        for (i, elem) in self.iter().enumerate() {
            if let Err(err) = elem.try_to_bytes_dynamic(input.clone(), &mut writer) {
                return Err(SerializeError::Field { name: format!("[{i}]"), err: Box::new(err) });
            }
        }
        Ok(())
    }
}
impl<T: TryToBytesDynamic<I>, I: Clone> TryToBytesDynamic<I> for [ T ]
where
    T::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize all of them in-order
        for (i, elem) in self.iter().enumerate() {
            if let Err(err) = elem.try_to_bytes_dynamic(input.clone(), &mut writer) {
                return Err(SerializeError::Field { name: format!("[{i}]"), err: Box::new(err) });
            }
        }
        Ok(())
    }
}
impl<T: TryToBytesDynamic<I>, I: Clone> TryToBytesDynamic<I> for Vec<T>
where
    T::Error: 'static,
{
    type Error = crate::errors::SerializeError;

    fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize all of them in-order
        for (i, elem) in self.iter().enumerate() {
            if let Err(err) = elem.try_to_bytes_dynamic(input.clone(), &mut writer) {
                return Err(SerializeError::Field { name: format!("[{i}]"), err: Box::new(err) });
            }
        }
        Ok(())
    }
}

// Implement for string-likes
impl TryToBytesDynamic<()> for str {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}
impl TryToBytesDynamic<()> for &str {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}
impl TryToBytesDynamic<()> for Cow<'_, str> {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}
impl TryToBytesDynamic<()> for String {
    type Error = crate::errors::SerializeError;

    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(SerializeError::Write { err }),
        }
    }
}



/// States that a type has a parsed length.
/// 
/// This is used by various provided and derived implementations of [`TryFromBytesDynamic`] and [`ToBytes`] to automatically discover offsets.
/// 
/// # Example
/// ```rust
/// use bytes::ParsedLength as _;
/// 
/// assert_eq!(42u32.parsed_length(), 4);
/// assert_eq!(42u64.parsed_length(), 8);
/// assert_eq!("Hello, world!".parsed_length(), 13);
/// ```
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
