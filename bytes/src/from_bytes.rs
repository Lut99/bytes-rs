//  SPEC.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:26:27
//  Last edited:
//    08 Oct 2023, 12:34:50
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


/***** HELPER MACROS *****/
/// Translates a list of types into a list of unit-types.
macro_rules! unitify {
    // Trivial base-case
    ($fty:ty) => { () };
    // Recursive case
    ($fty:ty, $($tys:ty),+) => { (), unitify!($($tys),+) };
}

/// Implements [`TryFromBytesDynamic`] for a tuple of the given size.
/// 
/// The size is denoted as a pair of typenames, .e.g,
/// ```ignore
/// // Implements for a tuple of length three
/// try_from_bytes_dynamic_tuple_impl!(T1, T2, T3);
/// ```
macro_rules! try_from_bytes_dynamic_tuple_impl {
    // Case for empty tuple (unit type)
    () => {
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
    };

    // Case for a single-element tuple
    (($fty:ident, $fin:ident, $ffi:tt)) => {
        impl<$fty: TryFromBytesDynamic<$fin>, $fin> TryFromBytesDynamic<$fin> for ($fty,)
        where
            $fty::Error: 'static,
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
            fn try_from_bytes_dynamic(input: $fin, reader: impl Read) -> Result<Self, Self::Error> {
                match $fty::try_from_bytes_dynamic(input, reader) {
                    Ok(inner) => Ok((inner,)),
                    Err(err)  => Err(Error::Field { name: stringify!($ffi).into(), err: Box::new(err) }),
                }
            }
        }        
    };

    // Case for more than one tuple
    (($fty:ident, $fin:ident, $ffi:tt), $(($tys:ident, $ins:ident, $fis:tt)),+) => {
        impl<$fty: TryFromBytesDynamic<()>, $($tys: TryFromBytesDynamic<()>),+> TryFromBytesDynamic<()> for ($fty, $($tys),+)
        where
            $fty::Error: 'static,
            $($tys::Error: 'static),+
        {
            type Error = Error;

            /// Parses that allows a tuple of [`TryFromBytes`]es to be [`TryFromBytes`] itself.
            /// 
            /// Specifically, just allows a single empty input to be given if all the sub-parsers only require empty inputs.
            ///
            /// This parser assumes the nested types are tightly packed, i.e., follow immediately one after another. You can explicitly keep areas empty by using the [`TryFromBytesDynamic<usize>`] overload of `()`.
            /// 
            /// # Arguments
            /// - `input`: The input to pass to the sub-parsers, or rather, which indicates no input is necessary.
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
            fn try_from_bytes_dynamic(_input: (), reader: impl Read) -> Result<Self, Self::Error> {
                Self::try_from_bytes_dynamic(((), $(unitify!($tys)),+), reader)
            }
        }
        impl<$fty: TryFromBytesDynamic<$fin>, $($tys: TryFromBytesDynamic<$ins>),+, $fin, $($ins),+> TryFromBytesDynamic<($fin, $($ins),+)> for ($fty, $($tys),+)
        where
            $fty::Error: 'static,
            $($tys::Error: 'static),+
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
            fn try_from_bytes_dynamic(input: ($fin, $($ins),+), mut reader: impl Read) -> Result<Self, Self::Error> {
                // Simply parse the fields one after another
                Ok((
                    match $fty::try_from_bytes_dynamic(input.$ffi, &mut reader) {
                        Ok(inner) => inner,
                        Err(err)  => { return Err(Error::Field { name: stringify!($ffi).into(), err: Box::new(err) }); },
                    },
                    $(match $tys::try_from_bytes_dynamic(input.$fis, &mut reader) {
                        Ok(inner) => inner,
                        Err(err)  => { return Err(Error::Field { name: stringify!($fis).into(), err: Box::new(err) }); },
                    }),+
                ))
            }
        }
    };
}





/***** ERRORS *****/
/// Defines errors that may occur when using library parsers.
/// 
/// Note that this struct is designed to report nested errors only when [`source()`](Error::source()) is called.
/// As such, consider using a library for reporting these easily (e.g., <https://github.com/Lut99/error-trace-rs>).
#[derive(Debug)]
pub enum Error {
    /// Couldn't read from the given reader.
    /// 
    /// This typically happens when there aren't enough bytes left to read, or if the underlying stream calls some error (e.g., when directly reading files).
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// 
    /// assert!(matches!(u8::try_from_bytes(&[][..]), Err(bytes::from_bytes::Error::Read { .. })));
    /// ```
    Read { err: std::io::Error },
    /// A sub-parser of a field failed.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes;
    /// 
    /// #[derive(TryFromBytes)]
    /// struct Example {
    ///     #[bytes]
    ///     field_1 : u32
    /// }
    /// 
    /// assert!(matches!(Example::try_from_bytes(&[][..]), Err(bytes::from_bytes::Error::Field{ .. })));
    /// ```
    Field { name: String, err: Box<dyn error::Error> },

    /// Given parsed byte was not a valid UTF-8 character.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// 
    /// assert!(matches!(char::try_from_bytes(&[ 0x00, 0x00, 0x00, 0xFF ][..]), Err(bytes::from_bytes::Error::NonUtf8Char { .. })));
    /// ```
    NonUtf8Char { raw: u32 },
    /// Given byte string was not valid UTF-8.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytesDynamic as _;
    /// 
    /// assert!(matches!(String::try_from_bytes_dynamic(4, &[ 0x00, 0x00, 0x00, 0xFF ][..]), Err(bytes::from_bytes::Error::NonUtf8String { .. })));
    /// ```
    NonUtf8String { err: std::string::FromUtf8Error },
}
impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use Error::*;
        match self {
            Read { .. }        => write!(f, "Failed to read from given reader"),
            Field { name, .. } => write!(f, "Failed to parse field '{name}'"),

            NonUtf8Char { raw }  => write!(f, "Byte '{raw:#010X}' is not a valid UTF-8 character"),
            NonUtf8String { .. } => write!(f, "Given bytes are not valid UTF-8"),
        }
    }
}
impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        use Error::*;
        match self {
            Read { err }      => Some(err),
            Field { err, .. } => Some(&**err),

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





/***** AUXILLARY *****/
/// Defines that a type can be parsed from a series of bytes.
/// 
/// This can be thought of as a non-configurable counterpart to the [`TryFromBytesDynamic`].
/// In fact, it is implemented as a more convenient alias for a dynamic implementation that takes `()` as input.
/// 
/// Typically, you can automatically derive this trait using the [`TryFromBytes`](crate::procedural::TryFromBytes)-macro.
/// 
/// # Example
/// ```rust
/// # use std::io::Read;
/// use bytes::{TryFromBytes as _, TryFromBytesDynamic};
/// 
/// struct Example {
///     num : u16,
/// }
/// impl TryFromBytesDynamic<()> for Example {
///     type Error = bytes::from_bytes::Error;
/// 
///     #[inline]
///     fn try_from_bytes_dynamic(input: (), reader: impl Read) -> Result<Self, Self::Error> {
///         Ok(Self {
///             num : u16::try_from_bytes_dynamic(input, reader)?,
///         })
///     }
/// }
/// 
/// assert_eq!(Example::try_from_bytes_dynamic((), &[ 0x00, 0x2A ][..]).unwrap().num, 10752);
/// // Equivalent and more convenient
/// assert_eq!(Example::try_from_bytes(&[ 0x00, 0x2A ][..]).unwrap().num, 10752);
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
    /// assert_eq!(u8::try_from_bytes(&[ 0x2A ][..]).unwrap(), 42);
    /// assert_eq!(i16::try_from_bytes(&[ 0x2A, 0x00 ][..]).unwrap(), 42);
    /// assert_eq!(<(u8, u8)>::try_from_bytes(&[ 0x00, 0x2A ][..]).unwrap(), (0, 42));
    /// ```
    fn try_from_bytes(reader: impl Read) -> Result<Self, Self::Error>;
}
impl<T: TryFromBytesDynamic<()>> TryFromBytes for T {
    /// Automatic implementation of `TryFromBytes` for [`TryFromBytesDynamic`]'s that take no input (`()`).
    #[inline]
    #[track_caller]
    fn try_from_bytes(reader: impl Read) -> Result<Self, Self::Error> { Self::try_from_bytes_dynamic((), reader) }
}





/***** LIBRARY *****/
/// Defines that a type can be parsed from a series of bytes, but requires additional input to do so.
/// 
/// This can be thought of as a configurable counterpart to the [`TryFromBytes`].
/// In fact, the [`TryFromBytes`] is an alias for `TryFromBytesDynamic<()>`.
/// 
/// Typically, you can automatically derive this trait using the [`TryFromBytesDynamic`](crate::procedural::TryFromBytesDynamic)-macro.
/// 
/// # Example
/// ```rust
/// # use std::io::Read;
/// use bytes::TryFromBytesDynamic;
/// 
/// struct Example {
///     num : u16,
/// }
/// impl TryFromBytesDynamic<Option<u16>> for Example {
///     type Error = bytes::from_bytes::Error;
/// 
///     #[inline]
///     fn try_from_bytes_dynamic(input: Option<u16>, bytes: impl Read) -> Result<Self, Self::Error> {
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
/// assert_eq!(Example::try_from_bytes_dynamic(Some(100), &[ 0x00, 0x2A ][..]).unwrap().num, 100);
/// assert_eq!(Example::try_from_bytes_dynamic(None, &[ 0x00, 0x2A ][..]).unwrap().num, 10752);
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
    /// assert_eq!(i16::try_from_bytes_dynamic(BigEndian, &[ 0x00, 0xFF ][..]).unwrap(), 255);
    /// assert_eq!(i16::try_from_bytes_dynamic(LittleEndian, &[ 0x00, 0xFF ][..]).unwrap(), -256);
    /// assert_eq!(String::try_from_bytes_dynamic(13, &[ 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ][..]).unwrap(), "Hello, world!");
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
    /// use bytes::TryFromBytesDynamic as _;
    /// 
    /// // This parses with native endianness, so we test based on which endianness is used
    /// #[cfg(target_endian = "big")]
    /// assert_eq!(u16::try_from_bytes_dynamic((), &[ 0x00, 0x2A ][..]).unwrap(), 42);
    /// #[cfg(target_endian = "little")]
    /// assert_eq!(u16::try_from_bytes_dynamic((), &[ 0x00, 0x2A ][..]).unwrap(), 10752);
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
    /// use bytes::{Endianness, TryFromBytesDynamic as _};
    /// 
    /// fn parse(input: &[u8], endianness: Endianness) -> u16 {
    ///     u16::try_from_bytes_dynamic(endianness, input).unwrap()
    /// }
    /// 
    /// assert_eq!(parse(&[ 0x00, 0x2A ], Endianness::Big), 42);
    /// assert_eq!(parse(&[ 0x00, 0x2A ], Endianness::Little), 10752);
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
    /// use bytes::{Endianness, TryFromBytesDynamic as _};
    /// 
    /// fn parse(input: &[u8], endianness: &Endianness) -> u16 {
    ///     u16::try_from_bytes_dynamic(endianness, input).unwrap()
    /// }
    /// 
    /// assert_eq!(parse(&[ 0x00, 0x2A ], &Endianness::Big), 42);
    /// assert_eq!(parse(&[ 0x00, 0x2A ], &Endianness::Little), 10752);
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
    /// use bytes::{Endianness, TryFromBytesDynamic as _};
    /// 
    /// fn parse(input: &[u8], endianness: &mut Endianness) -> u16 {
    ///     u16::try_from_bytes_dynamic(endianness, input).unwrap()
    /// }
    /// 
    /// assert_eq!(parse(&[ 0x00, 0x2A ], &mut Endianness::Big), 42);
    /// assert_eq!(parse(&[ 0x00, 0x2A ], &mut Endianness::Little), 10752);
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
try_from_bytes_dynamic_tuple_impl!();
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0));
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1));
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2));
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3));
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4));
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4), (T6, I6, 5));
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4), (T6, I6, 5), (T7, I7, 6));
try_from_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4), (T6, I6, 5), (T7, I7, 6), (T8, I8, 7));
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
        match String::from_utf8(bytes) {
            Ok(res)  => Ok(res),
            Err(err) => Err(Error::NonUtf8String { err }),
        }
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
