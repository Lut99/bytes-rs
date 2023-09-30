//  SPEC.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:26:27
//  Last edited:
//    30 Sep 2023, 14:02:39
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the (public) interfaces and structs for this crate.
// 

use std::borrow::Cow;
use std::error;
use std::fmt::{Display, Formatter, Result as FResult};
use std::io::Read;

use crate::order::{BigEndian, Endianness, LittleEndian};
use crate::string::{Lossiness, Lossy, NonLossy};


/***** ERRORS *****/
/// Defines errors that may occur when using library parsers.
/// 
/// Note that this struct is designed to report nested errors only when [`source()`](Error::source()) is called.
/// As such, consider using a library for reporting these easily (e.g., <https://github.com/Lut99/error-trace-rs>).
#[derive(Debug)]
pub enum Error {
    /// Couldn't read from the given reader.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    Read { err: std::io::Error },

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
    Field { name: String, err: Box<dyn error::Error> },

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
impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use Error::*;
        match self {
            Read { .. }                    => write!(f, "Failed to read from given reader"),
            Field { name, .. }             => write!(f, "Failed to parse field '{name}'"),

            NonUtf8Char { raw }  => write!(f, "Byte '{raw:#010X}' is not a valid UTF-8 character"),
            NonUtf8String { .. } => write!(f, "Given bytes are not valid UTF-8"),
        }
    }
}
impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        use Error::*;
        match self {
            Read { err }          => Some(err),
            Field { err, .. }     => Some(&**err),

            NonUtf8Char { .. }    => None,
            NonUtf8String { err } => Some(err),
        }
    }
}





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





/***** LIBRARY *****/
/// Defines that a type can be parsed from a series of bytes.
/// 
/// This can be thought of as a non-erroring, non-configurable counterpart to the [`TryFromBytesDynamic`].
/// In fact, it is implemented as a more convenient alias for a dynamic implementation that takes `()` as input and has [`Infallible`](std::convert::Infallible) as error type.
/// 
/// Typically, you can automatically derive this trait using the [`FromBytes`](crate::procedural::FromBytes)-macro.
/// 
/// # Example
/// ```rust
/// # use std::io::Read;
/// use bytes::{FromBytes as _, TryFromBytesDynamic};
/// 
/// struct Example {
///     num : u16,
/// }
/// impl TryFromBytesDynamic<()> for Example {
///     type Error = std::convert::Infallible;
/// 
///     #[inline]
///     fn try_from_bytes_dynamic(input: (), mut reader: impl Read) -> Result<Self, Self::Error> {
///         Ok(Self {
///             num : u16::try_from_bytes_dynamic(input, reader).unwrap(),
///         })
///     }
/// }
/// 
/// assert_eq!(Example::try_from_bytes_dynamic((), &[ 0x00, 0x2A ]).unwrap().num, 10752);
/// // Equivalent and more convenient
/// assert_eq!(Example::from_bytes(&[ 0x00, 0x2A ]).num, 10752);
/// ```
pub trait FromBytes: TryFromBytesDynamic<(), Error = std::convert::Infallible> {
    /// Parses ourselves from the given bytes.
    /// 
    /// # Arguments
    /// - `reader`: The [`Read`]er object to parse from.
    /// 
    /// # Returns
    /// A new instance of Self parsed from the given bytes.
    /// 
    /// # Examples
    /// ```rust
    /// use bytes::FromBytes as _;
    /// 
    /// assert_eq!(<()>::try_from_bytes(&[]), ());
    /// ```
    fn from_bytes(bytes: impl Read) -> Self;
}
impl<T: TryFromBytesDynamic<(), Error = std::convert::Infallible>> FromBytes for T {
    /// Automatic implementation of `FromBytes` for [`TryFromBytesDynamic`]'s that take no input (`()`) and do not error ([`std::convert::Infallible`]).
    #[inline]
    #[track_caller]
    fn from_bytes(reader: impl Read) -> Self { Self::try_from_bytes_dynamic((), reader).unwrap() }
}



/// Defines that a type can be parsed from a series of bytes, but requires additional input to do so.
/// 
/// This can be thought of as a non-erroring counterpart to the [`TryFromBytesDynamic`].
/// In fact, it is implemented as a more convenient alias for an implementation that has [`Infallible`](std::convert::Infallible) as error type.
/// 
/// Typically, you can automatically derive this trait using the [`FromBytesDynamic`](crate::procedural::FromBytesDynamic)-macro.
/// 
/// # Example
/// ```rust
/// # use std::io::Read;
/// use bytes::{FromBytesDynamic as _, TryFromBytesDynamic};
/// 
/// struct Example {
///     data : Vec<u8>,
/// }
/// impl TryFromBytesDynamic<usize> for Example {
///     type Error = std::convert::Infallible;
/// 
///     #[inline]
///     fn try_from_bytes_dynamic(input: usize, mut reader: impl Read) -> Result<Self, Self::Error> {
///         Ok(Self {
///             num : Vec::try_from_bytes_dynamic((input, ()), reader).unwrap(),
///         })
///     }
/// }
/// 
/// assert_eq!(Example::try_from_bytes_dynamic((2, ()), &[ 0x00, 0x2A ]).unwrap().data, vec![ 0x00, 0x2A ]);
/// // Equivalent and more convenient
/// assert_eq!(Example::from_bytes_dynamic(2, &[ 0x00, 0x2A ]).data, vec![ 0x00, 0x2A ]);
/// ```
pub trait FromBytesDynamic<I>: TryFromBytesDynamic<I, Error = std::convert::Infallible> {
    /// Parses ourselves from the given input and bytes.
    /// 
    /// # Arguments
    /// - `input`: The additional input needed to make sense of this, like some length.
    /// - `reader`: The [`Read`]er object to parse from.
    /// 
    /// # Returns
    /// A new instance of Self parsed from the given bytes.
    /// 
    /// # Examples
    /// See the documentation for the trait itself for an example.
    fn from_bytes_dynamic(input: I, bytes: impl Read) -> Self;
}
impl<T: TryFromBytesDynamic<I, Error = std::convert::Infallible>, I> FromBytesDynamic<I> for T {
    /// Automatic implementation of `FromBytes` for [`TryFromBytesDynamic`]'s that take no input (`()`) and do not error ([`std::convert::Infallible`]).
    #[inline]
    #[track_caller]
    fn from_bytes_dynamic(input: I, reader: impl Read) -> Self { Self::try_from_bytes_dynamic(input, reader).unwrap() }
}



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
    type Error: error::Error;


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
    type Error = Error;

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
        let mut bytes: [ u8; LENGTH ] = [ 0; LENGTH ];
        if let Err(err) = reader.read_exact(&mut bytes) {
            return Err(Error::Read { err });
        }

        // Now simply parse the bytes
        Ok(Self::from_ne_bytes(&bytes))
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<Endianness> for T {
    type Error = Error;

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
    type Error = Error;

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
    type Error = Error;

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
    type Error = Error;

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
            return Err(Error::Read { err });
        }

        // Now simply parse the bytes
        Ok(Self::from_be_bytes(&bytes))
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<&BigEndian> for T {
    type Error = Error;

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
    fn try_from_bytes_dynamic(input: &BigEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<&mut BigEndian> for T {
    type Error = Error;

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
    fn try_from_bytes_dynamic(input: &mut BigEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<LittleEndian> for T {
    type Error = Error;

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
            return Err(Error::Read { err });
        }

        // Now simply parse the bytes
        Ok(Self::from_le_bytes(&bytes))
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<&LittleEndian> for T {
    type Error = Error;

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
    fn try_from_bytes_dynamic(input: &LittleEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl<const LENGTH: usize, T: PrimitiveFromBytes + num_traits::FromBytes<Bytes = [u8; LENGTH]>> TryFromBytesDynamic<&mut LittleEndian> for T {
    type Error = Error;

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
    fn try_from_bytes_dynamic(input: &mut LittleEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<()> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using native endianness. If you want to commit to a particular one, give [`BigEndian`] or [`LittleEndian`] as input.
    /// 
    /// # Arguments
    /// - `input`: Any configurable input to this parser, which is none.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_from_bytes_dynamic(input: (), reader: impl Read) -> Result<Self, Self::Error> {
        // First, parse a u32 as base
        let res: u32 = u32::try_from_bytes_dynamic(input, reader)?;

        // Then, parse as char
        match char::from_u32(res) {
            Some(res) => Ok(res),
            None      => Err(Error::NonUtf8Char { raw: res }),
        }
    }
}
impl TryFromBytesDynamic<Endianness> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines if we will be parsing the [`u32`] in big-endian or little-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: Endianness, reader: impl Read) -> Result<Self, Self::Error> {
        match input {
            Endianness::Big    => Self::try_from_bytes_dynamic(BigEndian, reader),
            Endianness::Little => Self::try_from_bytes_dynamic(LittleEndian, reader),
        }
    }
}
impl TryFromBytesDynamic<&Endianness> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines if we will be parsing the [`u32`] in big-endian or little-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
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
impl TryFromBytesDynamic<&mut Endianness> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines if we will be parsing the [`u32`] in big-endian or little-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
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
impl TryFromBytesDynamic<BigEndian> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines we will be parsing the [`u32`] in big-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: BigEndian, reader: impl Read) -> Result<Self, Self::Error> {
        // First, parse a u32 as base
        let res: u32 = u32::try_from_bytes_dynamic(input, reader)?;

        // Then, parse as char
        match char::from_u32(res) {
            Some(res) => Ok(res),
            None      => Err(Error::NonUtf8Char { raw: res }),
        }
    }
}
impl TryFromBytesDynamic<&BigEndian> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines we will be parsing the [`u32`] in big-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &BigEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut BigEndian> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines we will be parsing the [`u32`] in big-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut BigEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<LittleEndian> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines we will be parsing the [`u32`] in little-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: LittleEndian, reader: impl Read) -> Result<Self, Self::Error> {
        // First, parse a u32 as base
        let res: u32 = u32::try_from_bytes_dynamic(input, reader)?;

        // Then, parse as char
        match char::from_u32(res) {
            Some(res) => Ok(res),
            None      => Err(Error::NonUtf8Char { raw: res }),
        }
    }
}
impl TryFromBytesDynamic<&LittleEndian> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines we will be parsing the [`u32`] in little-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &LittleEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut LittleEndian> for char {
    type Error = Error;

    /// Parses a single [`char`] from the given input stream.
    /// 
    /// Note that individual chars are always parsed as [`u32`]s and then converted to UTF-8.
    /// 
    /// This parser parses the [`u32`] using little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines we will be parsing the [`u32`] in little-endian byte order.
    /// - `reader`: The [`Read`]er to read from.
    /// 
    /// # Returns
    /// A new [`char`] parsed from the given `reader`.
    /// 
    /// # Errors
    /// This function may error if we failed to parse a [`u32`] or if the parsed [`u32`] was not a valid [`char`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut LittleEndian, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
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
    type Error = Error;

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
            Err(err) => Err(Error::Read { err }),
        }
    }
}
impl<T: TryFromBytesDynamic<I>, I> TryFromBytesDynamic<I> for (T,)
where
    T::Error: 'static,
{
    type Error = Error;

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
            Err(err)  => Err(Error::Field { name: "0".into(), err: Box::new(err) }),
        }
    }
}
impl<T1: TryFromBytesDynamic<I1>, T2: TryFromBytesDynamic<I2>, I1, I2> TryFromBytesDynamic<(I1, I2)> for (T1, T2)
where
    T1::Error: 'static,
    T2::Error: 'static,
{
    type Error = Error;

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
                Err(err)  => { return Err(Error::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "1".into(), err: Box::new(err) }); },
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
    type Error = Error;

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
                Err(err)  => { return Err(Error::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "2".into(), err: Box::new(err) }); },
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
    type Error = Error;

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
                Err(err)  => { return Err(Error::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "3".into(), err: Box::new(err) }); },
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
    type Error = Error;

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
                Err(err)  => { return Err(Error::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "4".into(), err: Box::new(err) }); },
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
    type Error = Error;

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
                Err(err)  => { return Err(Error::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "4".into(), err: Box::new(err) }); },
            },
            match T6::try_from_bytes_dynamic(input.5, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "5".into(), err: Box::new(err) }); },
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
    type Error = Error;

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
                Err(err)  => { return Err(Error::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "4".into(), err: Box::new(err) }); },
            },
            match T6::try_from_bytes_dynamic(input.5, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "5".into(), err: Box::new(err) }); },
            },
            match T7::try_from_bytes_dynamic(input.6, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "6".into(), err: Box::new(err) }); },
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
    type Error = Error;

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
                Err(err)  => { return Err(Error::Field { name: "0".into(), err: Box::new(err) }); },
            },
            match T2::try_from_bytes_dynamic(input.1, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "1".into(), err: Box::new(err) }); },
            },
            match T3::try_from_bytes_dynamic(input.2, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "2".into(), err: Box::new(err) }); },
            },
            match T4::try_from_bytes_dynamic(input.3, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "3".into(), err: Box::new(err) }); },
            },
            match T5::try_from_bytes_dynamic(input.4, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "4".into(), err: Box::new(err) }); },
            },
            match T6::try_from_bytes_dynamic(input.5, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "5".into(), err: Box::new(err) }); },
            },
            match T7::try_from_bytes_dynamic(input.6, &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "6".into(), err: Box::new(err) }); },
            },
            match T8::try_from_bytes_dynamic(input.7, reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: "7".into(), err: Box::new(err) }); },
            },
        ))
    }
}
impl<const LEN: usize, T: for<'a> TryFromBytesDynamic<&'a I>, I: AsRef<I>> TryFromBytesDynamic<I> for [ T; LEN ]
where
    for<'a> <T as TryFromBytesDynamic<&'a I>>::Error: 'static,
{
    type Error = Error;

    /// Parses an array of a nested TryFromBytesDynamic type.
    ///
    /// This parser assumes the elements are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using a tuple with the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: The input to each of the parsers. It is passed by reference (i.e., [`input.as_ref()`](AsRef<I>)) such that the parsers can clone as necessary.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// An array with parsed instances of the inner type.
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
            res[i] = match T::try_from_bytes_dynamic(input.as_ref(), &mut reader) {
                Ok(inner) => Some(inner),
                Err(err)  => { return Err(Error::Field { name: format!("[{i}]"), err: Box::new(err) }); },
            };
        }
        Ok(res.map(|elem| elem.unwrap()))
    }
}
impl<T: for<'a> TryFromBytesDynamic<&'a I>, I: AsRef<I>> TryFromBytesDynamic<(usize, I)> for Vec<T>
where
    for<'a> <T as TryFromBytesDynamic<&'a I>>::Error: 'static,
{
    type Error = Error;

    /// Parses a vector of a nested TryFromBytesDynamic type.
    ///
    /// This parser assumes the elements are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using a tuple with the [`TryFromBytesDynamic<usize>`] overload of `()`.
    /// 
    /// # Arguments
    /// - `input`: A tuple with the number of elements to parse first, and then the input to each of the parsers. It is passed by reference (i.e., [`input.1.as_ref()`](AsRef<I>)) such that the parsers can clone as necessary.
    /// - `reader`: The reader where the inner parsers will gets their bytes from.
    /// 
    /// # Returns
    /// A vector with parsed instances of the inner type.
    /// 
    /// # Errors
    /// This function errors whenever any child parser errors. It will be wrapped in a [`ParseError::Field`] in that case.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_from_bytes_dynamic(input: (usize, I), mut reader: impl Read) -> Result<Self, Self::Error> {
        // Simply parse all of them in-order
        let mut res: Vec<T> = Vec::with_capacity(input.0);
        for i in 0..input.0 {
            res.push(match T::try_from_bytes_dynamic(input.1.as_ref(), &mut reader) {
                Ok(inner) => inner,
                Err(err)  => { return Err(Error::Field { name: format!("[{i}]"), err: Box::new(err) }); },
            });
        }
        Ok(res)
    }
}

// Implement for string-likes
impl TryFromBytesDynamic<usize> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// Note that this default to non-lossy parsing. To parse lossy, consider using [`Lossy`] instead of [`usize`] as input size.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: usize, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(NonLossy(input), reader)
    }
}
impl TryFromBytesDynamic<Lossiness> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// The given [`Lossiness`] enum determines if we're parsing [lossy](Lossy) or [non-lossy](NonLossy).
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if we're parsing non-lossy and the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: Lossiness, reader: impl Read) -> Result<Self, Self::Error> {
        match input {
            Lossiness::Lossy(l)    => Self::try_from_bytes_dynamic(Lossy(l), reader),
            Lossiness::NonLossy(n) => Self::try_from_bytes_dynamic(NonLossy(n), reader),
        }
    }
}
impl TryFromBytesDynamic<&Lossiness> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// The given [`Lossiness`] enum determines if we're parsing [lossy](Lossy) or [non-lossy](NonLossy).
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if we're parsing non-lossy and the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &Lossiness, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut Lossiness> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// The given [`Lossiness`] enum determines if we're parsing [lossy](Lossy) or [non-lossy](NonLossy).
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if we're parsing non-lossy and the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut Lossiness, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<Lossy> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// This will parse the bytes as UTF-8 in a lossy manner. To throw errors when this fails, use [`NonLossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: Lossy, reader: impl Read) -> Result<Self, Self::Error> {
        Ok(Cow::Owned(String::try_from_bytes_dynamic(input, reader)?))
    }
}
impl TryFromBytesDynamic<&Lossy> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// This will parse the bytes as UTF-8 in a lossy manner. To throw errors when this fails, use [`NonLossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &Lossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut Lossy> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// This will parse the bytes as UTF-8 in a lossy manner. To throw errors when this fails, use [`NonLossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut Lossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<NonLossy> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// This will parse the bytes as UTF-8 in a non-lossy manner. To not errors when this fails but instead use weird characters, use [`Lossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: NonLossy, reader: impl Read) -> Result<Self, Self::Error> {
        Ok(Cow::Owned(String::try_from_bytes_dynamic(input, reader)?))
    }
}
impl TryFromBytesDynamic<&NonLossy> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// This will parse the bytes as UTF-8 in a non-lossy manner. To not errors when this fails but instead use weird characters, use [`Lossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &NonLossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut NonLossy> for Cow<'_, str> {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// This will parse the bytes as UTF-8 in a non-lossy manner. To not errors when this fails but instead use weird characters, use [`Lossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut NonLossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<usize> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// Note that this default to non-lossy parsing. To parse lossy, consider using [`Lossy`] instead of [`usize`] as input size.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: usize, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(NonLossy(input), reader)
    }
}
impl TryFromBytesDynamic<Lossiness> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// The given [`Lossiness`] enum determines if we're parsing [lossy](Lossy) or [non-lossy](NonLossy).
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if we're parsing non-lossy and the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: Lossiness, reader: impl Read) -> Result<Self, Self::Error> {
        match input {
            Lossiness::Lossy(l)    => Self::try_from_bytes_dynamic(Lossy(l), reader),
            Lossiness::NonLossy(n) => Self::try_from_bytes_dynamic(NonLossy(n), reader),
        }
    }
}
impl TryFromBytesDynamic<&Lossiness> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`Cow::Owned`].
    /// 
    /// The given [`Lossiness`] enum determines if we're parsing [lossy](Lossy) or [non-lossy](NonLossy).
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`Cow::Owned`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if we're parsing non-lossy and the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &Lossiness, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut Lossiness> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// The given [`Lossiness`] enum determines if we're parsing [lossy](Lossy) or [non-lossy](NonLossy).
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if we're parsing non-lossy and the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut Lossiness, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<Lossy> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// This will parse the bytes as UTF-8 in a lossy manner. To throw errors when this fails, use [`NonLossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: Lossy, mut reader: impl Read) -> Result<Self, Self::Error> {
        // Attempt to read enough information
        let mut bytes: Vec<u8> = vec![ 0; input.0 ];
        if let Err(err) = reader.read_exact(&mut bytes) {
            return Err(Error::Read { err });
        }

        // Now simply parse the bytes as a string
        match String::from_utf8(bytes) {
            Ok(res)  => Ok(res),
            Err(err) => Err(Error::NonUtf8String { err }),
        }
    }
}
impl TryFromBytesDynamic<&Lossy> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// This will parse the bytes as UTF-8 in a lossy manner. To throw errors when this fails, use [`NonLossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &Lossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut Lossy> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// This will parse the bytes as UTF-8 in a lossy manner. To throw errors when this fails, use [`NonLossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut Lossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<NonLossy> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// This will parse the bytes as UTF-8 in a non-lossy manner. To not errors when this fails but instead use weird characters, use [`Lossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: NonLossy, mut reader: impl Read) -> Result<Self, Self::Error> {
        // Attempt to read enough information
        let mut bytes: Vec<u8> = vec![ 0; input.0 ];
        if let Err(err) = reader.read_exact(&mut bytes) {
            return Err(Error::Read { err });
        }

        // Now simply parse the bytes as a string
        Ok(String::from_utf8_lossy(&bytes).to_string())
    }
}
impl TryFromBytesDynamic<&NonLossy> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// This will parse the bytes as UTF-8 in a non-lossy manner. To not errors when this fails but instead use weird characters, use [`Lossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &NonLossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
impl TryFromBytesDynamic<&mut NonLossy> for String {
    type Error = Error;

    /// Parses a dynamically sized string and returns it as a [`String`].
    /// 
    /// This will parse the bytes as UTF-8 in a non-lossy manner. To not errors when this fails but instead use weird characters, use [`Lossy`] as input instead.
    /// 
    /// # Arguments
    /// - `input`: The number of bytes to parse from the `reader`. All of these bytes will be interpreted as a UTF-8 string.
    /// - `reader`: The [`Read`]er we're getting bytes to parse from.
    /// 
    /// # Returns
    /// A new [`String`] containing the parsed string.
    /// 
    /// # Errors
    /// This function may error if we failed to get the required number of bytes from the `reader` or if the parsed bytes are not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_from_bytes_dynamic(input: &mut NonLossy, reader: impl Read) -> Result<Self, Self::Error> {
        Self::try_from_bytes_dynamic(*input, reader)
    }
}
