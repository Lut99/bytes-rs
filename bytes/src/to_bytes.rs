//  TO BYTES.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 11:30:12
//  Last edited:
//    30 Sep 2023, 14:19:33
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines the [`TryToBytesDynamic`] trait and friends.
// 

use std::borrow::Cow;
use std::error;
use std::fmt::{Display, Formatter, Result as FResult};
use std::io::Write;

use crate::order::{BigEndian, Endianness, LittleEndian};


/***** ERRORS *****/
/// Defines errors that may occur when using library serializers.
/// 
/// Note that this struct is designed to report nested errors only when [`source()`](Error::source()) is called.
/// As such, consider using a library for reporting these easily (e.g., <https://github.com/Lut99/error-trace-rs>).
#[derive(Debug)]
pub enum Error {
    /// Couldn't write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    Write { err: std::io::Error },
    /// A sub-serializer of a field failed.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes;
    /// use bytes::errors::ParseError;
    /// 
    /// #[derive(ToBytes)]
    /// struct Example {
    ///     #[bytes]
    ///     field_1 : u32
    /// }
    /// 
    /// assert!(matches!(Example::to_bytes(&mut []), Err(ParseError::Field{ .. })));
    /// ```
    Field { name: String, err: Box<dyn error::Error> },
}
impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        use Error::*;
        match self {
            Write { .. }       => write!(f, "Failed to write to given writer"),
            Field { name, .. } => write!(f, "Failed to serialize field '{name}'"),
        }
    }
}
impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        use Error::*;
        match self {
            Write { err }     => Some(err),
            Field { err, .. } => Some(&**err),
        }
    }
}





/***** HELPERS *****/
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





/***** AUXILLARY *****/
/// Allows a type to be serialized to bytes.
/// 
/// This trait acts as an alias for [`TryToBytesDynamic`] in scenario's where no input is required (i.e., `()`).
/// As such, it is automatically implemented for that cases.
/// 
/// This can be automatically derived using the [`TryToBytes`](crate::procedural::TryToBytes)-macro.
/// 
/// # Example
/// ```rust
/// todo!();
/// ```
pub trait TryToBytes: TryToBytesDynamic<()> {
    /// Attempts to serialize ourselves to a stream of bytes.
    /// 
    /// # Arguments
    /// - `writer`: The [output stream](std::io::Write) to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the given bytes.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_to_bytes(&self, writer: impl Write) -> Result<(), Self::Error>;
}
impl<T: TryToBytesDynamic<()>> TryToBytes for T {
    /// Automatic implementation for types implementing [`TryToBytesDynamic`] but require no input (i.e., `()`).
    #[inline]
    fn try_to_bytes(&self, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic((), writer)
    }
}





/***** LIBRARY *****/
/// Allows a type to be serialized to bytes, using some additional input for configuration.
/// 
/// This can be automatically derived using the [`TryToBytesDynamic`](crate::procedural::TryToBytesDynamic)-macro.
/// 
/// # Example
/// ```rust
/// todo!();
/// ```
pub trait TryToBytesDynamic<I> {
    /// The type of error that may occur when serializing.
    type Error: error::Error;


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
    type Error = Error;

    /// Serializes a primitive to native endianness.
    /// 
    /// To use a specific endianness, give [`BigEndian`] or [`LittleEndian`] as input.
    /// 
    /// # Arguments
    /// - `input`: Ignored, since this parser does not assume input.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply call the trait thingy
        match writer.write_all(self.to_ne_bytes().as_ref()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<Endianness> for T {
    type Error = Error;

    /// Serializes a primitive to a dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines whether we serialize to [big-endian](BigEndian) or [little-endian](LittleEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: Endianness, writer: impl Write) -> Result<(), Self::Error> {
        // Delegate to the hardcoded implementations
        match input {
            Endianness::Big    => self.try_to_bytes_dynamic(BigEndian, writer),
            Endianness::Little => self.try_to_bytes_dynamic(LittleEndian, writer),
        }
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<&Endianness> for T {
    type Error = Error;

    /// Serializes a primitive to a dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines whether we serialize to [big-endian](BigEndian) or [little-endian](LittleEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &Endianness, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<&mut Endianness> for T {
    type Error = Error;

    /// Serializes a primitive to a dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines whether we serialize to [big-endian](BigEndian) or [little-endian](LittleEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &mut Endianness, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<BigEndian> for T {
    type Error = Error;

    /// Serializes a primitive to big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines that we serialize to [big-endian](BigEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: BigEndian, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply call the trait thingy
        match writer.write_all(self.to_be_bytes().as_ref()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<&BigEndian> for T {
    type Error = Error;

    /// Serializes a primitive to big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines that we serialize to [big-endian](BigEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &BigEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<&mut BigEndian> for T {
    type Error = Error;

    /// Serializes a primitive to big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines that we serialize to [big-endian](BigEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &mut BigEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<LittleEndian> for T {
    type Error = Error;

    /// Serializes a primitive to little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines that we serialize to [little-endian](LittleEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: LittleEndian, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply call the trait thingy
        match writer.write_all(self.to_le_bytes().as_ref()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<&LittleEndian> for T {
    type Error = Error;

    /// Serializes a primitive to little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines that we serialize to [little-endian](LittleEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl<T: PrimitiveToBytes> TryToBytesDynamic<&mut LittleEndian> for T {
    type Error = Error;

    /// Serializes a primitive to little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines that we serialize to [little-endian](LittleEndian) byte order.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &mut LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl TryToBytesDynamic<()> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in native endianness.
    /// 
    /// # Arguments
    /// - `input`: Any input to configure this serializer, which is nothing.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (), writer: impl Write) -> Result<(), Self::Error> {
        // Serialize as a u32
        (*self as u32).try_to_bytes_dynamic(input, writer)
    }
}
impl TryToBytesDynamic<Endianness> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines if we will serialize the [`char`] in big-endian or little-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: Endianness, writer: impl Write) -> Result<(), Self::Error> {
        // Serialize as a u32
        (*self as u32).try_to_bytes_dynamic(input, writer)
    }
}
impl TryToBytesDynamic<&Endianness> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines if we will serialize the [`char`] in big-endian or little-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &Endianness, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl TryToBytesDynamic<&mut Endianness> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in dynamic endianness.
    /// 
    /// # Arguments
    /// - `input`: The [`Endianness`] that determines if we will serialize the [`char`] in big-endian or little-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &mut Endianness, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl TryToBytesDynamic<BigEndian> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines we will serialize the [`char`] in big-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: BigEndian, writer: impl Write) -> Result<(), Self::Error> {
        // Serialize as a u32
        (*self as u32).try_to_bytes_dynamic(input, writer)
    }
}
impl TryToBytesDynamic<&BigEndian> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines we will serialize the [`char`] in big-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &BigEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl TryToBytesDynamic<&mut BigEndian> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in big-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`BigEndian`] that determines we will serialize the [`char`] in big-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &mut BigEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl TryToBytesDynamic<LittleEndian> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines we will serialize the [`char`] in little-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
        // Serialize as a u32
        (*self as u32).try_to_bytes_dynamic(input, writer)
    }
}
impl TryToBytesDynamic<&LittleEndian> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines we will serialize the [`char`] in little-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}
impl TryToBytesDynamic<&mut LittleEndian> for char {
    type Error = Error;

    /// Serializes this character to the given byte stream.
    /// 
    /// Note that individual [`char`]s are always encoded as [`u32`]s.
    /// 
    /// This serializer serializes the [`char`] in little-endian byte order.
    /// 
    /// # Arguments
    /// - `input`: The [`LittleEndian`] that determines we will serialize the [`char`] in little-endian byte order.
    /// - `writer`: The [`Write`]r to serialize to.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the equivalent [`u32`].
    #[inline]
    fn try_to_bytes_dynamic(&self, input: &mut LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(*input, writer)
    }
}

// Implement it for tightly-packed containers
impl TryToBytesDynamic<()> for () {
    type Error = std::convert::Infallible;

    /// Dummy serializer that doesn't do anything.
    /// 
    /// This is useful for completeness purposes.
    /// 
    /// # Arguments
    /// - `input`: No input required, ignored.
    /// - `writer`: A [`Write`]r that we do not touch.
    /// 
    /// # Errors
    /// This function does not error (hence it relying on [`Infallible`](std::convert::Infallible)).
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), _writer: impl Write) -> Result<(), Self::Error> {
        Ok(())
    }
}
impl TryToBytesDynamic<usize> for () {
    type Error = Error;

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
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl<T: TryToBytesDynamic<I>, I> TryToBytesDynamic<I> for (T,)
where
    T::Error: 'static,
{
    type Error = Error;

    /// Serializes the inner value in a tuple with only one element.
    /// 
    /// This is useful for... well... completeness purposes, I guess?
    /// 
    /// # Arguments
    /// - `input`: The input to pass to the inner serializer.
    /// - `writer`: The [`Write`]r to which we serialize the inner value.
    /// 
    /// # Errors
    /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: I, writer: impl Write) -> Result<(), Self::Error> {
        match self.0.try_to_bytes_dynamic(input, writer) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Field { name: "0".into(), err: Box::new(err) }),
        }
    }
}
impl<T1: TryToBytesDynamic<I1>, T2: TryToBytesDynamic<I2>, I1, I2> TryToBytesDynamic<(I1, I2)> for (T1, T2)
where
    T1::Error: 'static,
    T2::Error: 'static,
{
    type Error = Error;

    /// Serializes a tuple of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: A tuple with inputs for each of the inner serializers. They are passed in-order, as-is.
    /// - `writer`: The [`Write`]r to which the inner serializes write.
    /// 
    /// # Errors
    /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(Error::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, writer) {
            return Err(Error::Field { name: "1".into(), err: Box::new(err) });
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
    type Error = Error;

    /// Serializes a tuple of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: A tuple with inputs for each of the inner serializers. They are passed in-order, as-is.
    /// - `writer`: The [`Write`]r to which the inner serializes write.
    /// 
    /// # Errors
    /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(Error::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(Error::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, writer) {
            return Err(Error::Field { name: "2".into(), err: Box::new(err) });
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
    type Error = Error;

    /// Serializes a tuple of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: A tuple with inputs for each of the inner serializers. They are passed in-order, as-is.
    /// - `writer`: The [`Write`]r to which the inner serializes write.
    /// 
    /// # Errors
    /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(Error::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(Error::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(Error::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, writer) {
            return Err(Error::Field { name: "3".into(), err: Box::new(err) });
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
    type Error = Error;

    /// Serializes a tuple of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: A tuple with inputs for each of the inner serializers. They are passed in-order, as-is.
    /// - `writer`: The [`Write`]r to which the inner serializes write.
    /// 
    /// # Errors
    /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(Error::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(Error::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(Error::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(Error::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, writer) {
            return Err(Error::Field { name: "4".into(), err: Box::new(err) });
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
    type Error = Error;

    /// Serializes a tuple of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: A tuple with inputs for each of the inner serializers. They are passed in-order, as-is.
    /// - `writer`: The [`Write`]r to which the inner serializes write.
    /// 
    /// # Errors
    /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5, I6), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(Error::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(Error::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(Error::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(Error::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, &mut writer) {
            return Err(Error::Field { name: "4".into(), err: Box::new(err) });
        }
        if let Err(err) = self.5.try_to_bytes_dynamic(input.5, writer) {
            return Err(Error::Field { name: "5".into(), err: Box::new(err) });
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
    type Error = Error;

    /// Serializes a tuple of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: A tuple with inputs for each of the inner serializers. They are passed in-order, as-is.
    /// - `writer`: The [`Write`]r to which the inner serializes write.
    /// 
    /// # Errors
    /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5, I6, I7), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(Error::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(Error::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(Error::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(Error::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, &mut writer) {
            return Err(Error::Field { name: "4".into(), err: Box::new(err) });
        }
        if let Err(err) = self.5.try_to_bytes_dynamic(input.5, &mut writer) {
            return Err(Error::Field { name: "5".into(), err: Box::new(err) });
        }
        if let Err(err) = self.6.try_to_bytes_dynamic(input.6, writer) {
            return Err(Error::Field { name: "6".into(), err: Box::new(err) });
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
    type Error = Error;

    /// Serializes a tuple of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: A tuple with inputs for each of the inner serializers. They are passed in-order, as-is.
    /// - `writer`: The [`Write`]r to which the inner serializes write.
    /// 
    /// # Errors
    /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: (I1, I2, I3, I4, I5, I6, I7, I8), mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize the fields one after another
        if let Err(err) = self.0.try_to_bytes_dynamic(input.0, &mut writer) {
            return Err(Error::Field { name: "0".into(), err: Box::new(err) });
        }
        if let Err(err) = self.1.try_to_bytes_dynamic(input.1, &mut writer) {
            return Err(Error::Field { name: "1".into(), err: Box::new(err) });
        }
        if let Err(err) = self.2.try_to_bytes_dynamic(input.2, &mut writer) {
            return Err(Error::Field { name: "2".into(), err: Box::new(err) });
        }
        if let Err(err) = self.3.try_to_bytes_dynamic(input.3, &mut writer) {
            return Err(Error::Field { name: "3".into(), err: Box::new(err) });
        }
        if let Err(err) = self.4.try_to_bytes_dynamic(input.4, &mut writer) {
            return Err(Error::Field { name: "4".into(), err: Box::new(err) });
        }
        if let Err(err) = self.5.try_to_bytes_dynamic(input.5, &mut writer) {
            return Err(Error::Field { name: "5".into(), err: Box::new(err) });
        }
        if let Err(err) = self.6.try_to_bytes_dynamic(input.6, &mut writer) {
            return Err(Error::Field { name: "6".into(), err: Box::new(err) });
        }
        if let Err(err) = self.7.try_to_bytes_dynamic(input.7, writer) {
            return Err(Error::Field { name: "7".into(), err: Box::new(err) });
        }
        Ok(())
    }
}
impl<const LEN: usize, T: for<'a> TryToBytesDynamic<&'a I>, I: AsRef<I>> TryToBytesDynamic<I> for [ T; LEN ]
where
    for<'a> <T as TryToBytesDynamic<&'a I>>::Error: 'static,
{
    type Error = Error;

    /// Serialies an array of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: The input to the nested serializer. It will be passed by reference (i.e., [`input.as_ref()`](AsRef<I>)) so that the serializer can clone it if necessary.
    /// - `writer`: The [`Write`]r to which the inner serializer writes.
    /// 
    /// # Errors
    /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize all of them in-order
        for (i, elem) in self.iter().enumerate() {
            if let Err(err) = elem.try_to_bytes_dynamic(input.as_ref(), &mut writer) {
                return Err(Error::Field { name: format!("[{i}]"), err: Box::new(err) });
            }
        }
        Ok(())
    }
}
impl<T: for<'a> TryToBytesDynamic<&'a I>, I: AsRef<I>> TryToBytesDynamic<I> for [ T ]
where
for<'a> <T as TryToBytesDynamic<&'a I>>::Error: 'static,
{
    type Error = Error;

    /// Serialies a slice of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: The input to the nested serializer. It will be passed by reference (i.e., [`input.as_ref()`](AsRef<I>)) so that the serializer can clone it if necessary.
    /// - `writer`: The [`Write`]r to which the inner serializer writes.
    /// 
    /// # Errors
    /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize all of them in-order
        for (i, elem) in self.iter().enumerate() {
            if let Err(err) = elem.try_to_bytes_dynamic(input.as_ref(), &mut writer) {
                return Err(Error::Field { name: format!("[{i}]"), err: Box::new(err) });
            }
        }
        Ok(())
    }
}
impl<T: for<'a> TryToBytesDynamic<&'a I>, I: AsRef<I>> TryToBytesDynamic<I> for Vec<T>
where
    for<'a> <T as TryToBytesDynamic<&'a I>>::Error: 'static,
{
    type Error = Error;

    /// Serialies a vector of inner values.
    /// 
    /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
    /// 
    /// # Arguments
    /// - `input`: The input to the nested serializer. It will be passed by reference (i.e., [`input.as_ref()`](AsRef<I>)) so that the serializer can clone it if necessary.
    /// - `writer`: The [`Write`]r to which the inner serializer writes.
    /// 
    /// # Errors
    /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`SerializeError::Field`].
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    fn try_to_bytes_dynamic(&self, input: I, mut writer: impl Write) -> Result<(), Self::Error> {
        // Simply serialize all of them in-order
        for (i, elem) in self.iter().enumerate() {
            if let Err(err) = elem.try_to_bytes_dynamic(input.as_ref(), &mut writer) {
                return Err(Error::Field { name: format!("[{i}]"), err: Box::new(err) });
            }
        }
        Ok(())
    }
}

// Implement for string-likes
impl TryToBytesDynamic<()> for str {
    type Error = Error;

    /// Serializes a string (as [`str`]) to a writer in UTF-8 encoding.
    /// 
    /// # Arguments
    /// - `input`: Nothing, since no input is required.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write the string's bytes to the given `writer`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl TryToBytesDynamic<()> for Cow<'_, str> {
    type Error = Error;

    /// Serializes a string (as [`Cow<str>`]) to a writer in UTF-8 encoding.
    /// 
    /// # Arguments
    /// - `input`: Nothing, since no input is required.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write the string's bytes to the given `writer`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl TryToBytesDynamic<()> for String {
    type Error = Error;

    /// Serializes a string (as [`String`]) to a writer in UTF-8 encoding.
    /// 
    /// # Arguments
    /// - `input`: Nothing, since no input is required.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if we failed to write the string's bytes to the given `writer`.
    /// 
    /// # Example
    /// ```rust
    /// todo!();
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: (), mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
