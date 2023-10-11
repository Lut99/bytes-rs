//  TO BYTES.rs
//    by Lut99
// 
//  Created:
//    30 Sep 2023, 11:30:12
//  Last edited:
//    11 Oct 2023, 21:46:34
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

use crate::no_input::NoInput;
use crate::order::{BigEndian, Endianness, LittleEndian};


/***** HELPER MACROS *****/
/// Implements [`TryToBytesDynamic`] for a primitive type.
macro_rules! try_to_bytes_dynamic_primitive_impl {
    // Special case: characters
    (char) => {
        impl TryToBytesDynamic<NoInput> for char {
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// // We parse using native endianness, so test with that in mind
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// #[cfg(target_endian = "big")]
            /// assert_eq!(buf, [0x00, 0x00, 0x00, 0x41]);
            /// #[cfg(target_endian = "little")]
            /// assert_eq!(buf, [0x41, 0x00, 0x00, 0x00]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: NoInput, writer: impl Write) -> Result<(), Self::Error> {
                // Serialize as a u32
                (*self as u32).try_to_bytes_dynamic(input, writer)
            }
        }
        impl TryToBytesDynamic<&NoInput> for char {
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// // We parse using native endianness, so test with that in mind
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// #[cfg(target_endian = "big")]
            /// assert_eq!(buf, [0x00, 0x00, 0x00, 0x41]);
            /// #[cfg(target_endian = "little")]
            /// assert_eq!(buf, [0x41, 0x00, 0x00, 0x00]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &NoInput, writer: impl Write) -> Result<(), Self::Error> {
                // Serialize as a u32
                (*self as u32).try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<&mut NoInput> for char {
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// // We parse using native endianness, so test with that in mind
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// #[cfg(target_endian = "big")]
            /// assert_eq!(buf, [0x00, 0x00, 0x00, 0x41]);
            /// #[cfg(target_endian = "little")]
            /// assert_eq!(buf, [0x41, 0x00, 0x00, 0x00]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &mut NoInput, writer: impl Write) -> Result<(), Self::Error> {
                // Serialize as a u32
                (*self as u32).try_to_bytes_dynamic(*input, writer)
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{Endianness, TryToBytesDynamic as _};
            /// 
            /// fn serialize<const LEN: usize>(value: char, endianness: Endianness) -> Result<[u8; LEN], bytes::to_bytes::Error> {
            ///     let mut buf: [u8; LEN] = [0; LEN];
            ///     value.try_to_bytes_dynamic(endianness, &mut buf[..])?;
            ///     Ok(buf)
            /// }
            /// 
            /// assert_eq!(serialize::<4>('A', Endianness::Big).unwrap(), [ 0x00, 0x00, 0x00, 0x41 ]);
            /// assert_eq!(serialize::<4>('A', Endianness::Little).unwrap(), [ 0x41, 0x00, 0x00, 0x00 ]);
            /// 
            /// assert!(matches!(serialize::<3>('A', Endianness::Big), Err(bytes::to_bytes::Error::Write { .. })));
            /// assert!(matches!(serialize::<3>('A', Endianness::Little), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{Endianness, TryToBytesDynamic as _};
            /// 
            /// fn serialize<const LEN: usize>(value: char, endianness: &Endianness) -> Result<[u8; LEN], bytes::to_bytes::Error> {
            ///     let mut buf: [u8; LEN] = [0; LEN];
            ///     value.try_to_bytes_dynamic(endianness, &mut buf[..])?;
            ///     Ok(buf)
            /// }
            /// 
            /// assert_eq!(serialize::<4>('A', &Endianness::Big).unwrap(), [ 0x00, 0x00, 0x00, 0x41 ]);
            /// assert_eq!(serialize::<4>('A', &Endianness::Little).unwrap(), [ 0x41, 0x00, 0x00, 0x00 ]);
            /// 
            /// assert!(matches!(serialize::<3>('A', &Endianness::Big), Err(bytes::to_bytes::Error::Write { .. })));
            /// assert!(matches!(serialize::<3>('A', &Endianness::Little), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{Endianness, TryToBytesDynamic as _};
            /// 
            /// fn serialize<const LEN: usize>(value: char, endianness: &mut Endianness) -> Result<[u8; LEN], bytes::to_bytes::Error> {
            ///     let mut buf: [u8; LEN] = [0; LEN];
            ///     value.try_to_bytes_dynamic(endianness, &mut buf[..])?;
            ///     Ok(buf)
            /// }
            /// 
            /// assert_eq!(serialize::<4>('A', &mut Endianness::Big).unwrap(), [ 0x00, 0x00, 0x00, 0x41 ]);
            /// assert_eq!(serialize::<4>('A', &mut Endianness::Little).unwrap(), [ 0x41, 0x00, 0x00, 0x00 ]);
            /// 
            /// assert!(matches!(serialize::<3>('A', &mut Endianness::Big), Err(bytes::to_bytes::Error::Write { .. })));
            /// assert!(matches!(serialize::<3>('A', &mut Endianness::Little), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x00, 0x00, 0x00, 0x41 ]);
            /// 
            /// let mut buf: [u8; 3] = [0; 3];
            /// assert!(matches!('A'.try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(&BigEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x00, 0x00, 0x00, 0x41 ]);
            /// 
            /// let mut buf: [u8; 3] = [0; 3];
            /// assert!(matches!('A'.try_to_bytes_dynamic(&BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(&mut BigEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x00, 0x00, 0x00, 0x41 ]);
            /// 
            /// let mut buf: [u8; 3] = [0; 3];
            /// assert!(matches!('A'.try_to_bytes_dynamic(&mut BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{LittleEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(LittleEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x41, 0x00, 0x00, 0x00 ]);
            /// 
            /// let mut buf: [u8; 3] = [0; 3];
            /// assert!(matches!('A'.try_to_bytes_dynamic(LittleEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{LittleEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(&LittleEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x41, 0x00, 0x00, 0x00 ]);
            /// 
            /// let mut buf: [u8; 3] = [0; 3];
            /// assert!(matches!('A'.try_to_bytes_dynamic(&LittleEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{LittleEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 4] = [0; 4];
            /// 'A'.try_to_bytes_dynamic(&mut LittleEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x41, 0x00, 0x00, 0x00 ]);
            /// 
            /// let mut buf: [u8; 3] = [0; 3];
            /// assert!(matches!('A'.try_to_bytes_dynamic(&mut LittleEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &mut LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }        
    };

    // Primitives
    ($pty:ident) => {
        impl TryToBytesDynamic<NoInput> for $pty {
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
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// // We parse using native endianness, so test with that in mind
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// #[cfg(target_endian = "big")]
            /// assert_eq!(buf, [0x00, 0x2A]);
            /// #[cfg(target_endian = "little")]
            /// assert_eq!(buf, [0x2A, 0x00]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, _input: NoInput, mut writer: impl Write) -> Result<(), Self::Error> {
                // Simply call the trait thingy
                match writer.write_all(self.to_ne_bytes().as_ref()) {
                    Ok(_)    => Ok(()),
                    Err(err) => Err(Error::Write { err }),
                }
            }
        }
        impl TryToBytesDynamic<&NoInput> for $pty {
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
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// // We parse using native endianness, so test with that in mind
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// #[cfg(target_endian = "big")]
            /// assert_eq!(buf, [0x00, 0x2A]);
            /// #[cfg(target_endian = "little")]
            /// assert_eq!(buf, [0x2A, 0x00]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &NoInput, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<&mut NoInput> for $pty {
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
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// // We parse using native endianness, so test with that in mind
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// #[cfg(target_endian = "big")]
            /// assert_eq!(buf, [0x00, 0x2A]);
            /// #[cfg(target_endian = "little")]
            /// assert_eq!(buf, [0x2A, 0x00]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &mut NoInput, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<Endianness> for $pty {
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
            /// use bytes::{Endianness, TryToBytesDynamic as _};
            /// 
            /// fn serialize<const LEN: usize>(value: u16, endianness: Endianness) -> Result<[u8; LEN], bytes::to_bytes::Error> {
            ///     let mut buf: [u8; LEN] = [0; LEN];
            ///     value.try_to_bytes_dynamic(endianness, &mut buf[..])?;
            ///     Ok(buf)
            /// }
            /// 
            /// assert_eq!(serialize::<2>(42, Endianness::Big).unwrap(), [ 0x00, 0x2A ]);
            /// assert_eq!(serialize::<2>(42, Endianness::Little).unwrap(), [ 0x2A, 0x00 ]);
            /// 
            /// assert!(matches!(serialize::<1>(42, Endianness::Big), Err(bytes::to_bytes::Error::Write { .. })));
            /// assert!(matches!(serialize::<1>(42, Endianness::Little), Err(bytes::to_bytes::Error::Write { .. })));
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
        impl TryToBytesDynamic<&Endianness> for $pty {
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
            /// use bytes::{Endianness, TryToBytesDynamic as _};
            /// 
            /// fn serialize<const LEN: usize>(value: u16, endianness: &Endianness) -> Result<[u8; LEN], bytes::to_bytes::Error> {
            ///     let mut buf: [u8; LEN] = [0; LEN];
            ///     value.try_to_bytes_dynamic(endianness, &mut buf[..])?;
            ///     Ok(buf)
            /// }
            /// 
            /// assert_eq!(serialize::<2>(42, &Endianness::Big).unwrap(), [ 0x00, 0x2A ]);
            /// assert_eq!(serialize::<2>(42, &Endianness::Little).unwrap(), [ 0x2A, 0x00 ]);
            /// 
            /// assert!(matches!(serialize::<1>(42, &Endianness::Big), Err(bytes::to_bytes::Error::Write { .. })));
            /// assert!(matches!(serialize::<1>(42, &Endianness::Little), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &Endianness, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<&mut Endianness> for $pty {
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
            /// use bytes::{Endianness, TryToBytesDynamic as _};
            /// 
            /// fn serialize<const LEN: usize>(value: u16, endianness: &mut Endianness) -> Result<[u8; LEN], bytes::to_bytes::Error> {
            ///     let mut buf: [u8; LEN] = [0; LEN];
            ///     value.try_to_bytes_dynamic(endianness, &mut buf[..])?;
            ///     Ok(buf)
            /// }
            /// 
            /// assert_eq!(serialize::<2>(42, &mut Endianness::Big).unwrap(), [ 0x00, 0x2A ]);
            /// assert_eq!(serialize::<2>(42, &mut Endianness::Little).unwrap(), [ 0x2A, 0x00 ]);
            /// 
            /// assert!(matches!(serialize::<1>(42, &mut Endianness::Big), Err(bytes::to_bytes::Error::Write { .. })));
            /// assert!(matches!(serialize::<1>(42, &mut Endianness::Little), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &mut Endianness, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<BigEndian> for $pty {
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
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x00, 0x2A ]);
            /// 
            /// let mut buf: [u8; 1] = [0; 1];
            /// assert!(matches!(42u16.try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
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
        impl TryToBytesDynamic<&BigEndian> for $pty {
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
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(&BigEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x00, 0x2A ]);
            /// 
            /// let mut buf: [u8; 1] = [0; 1];
            /// assert!(matches!(42u16.try_to_bytes_dynamic(&BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &BigEndian, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<&mut BigEndian> for $pty {
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
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(&mut BigEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x00, 0x2A ]);
            /// 
            /// let mut buf: [u8; 1] = [0; 1];
            /// assert!(matches!(42u16.try_to_bytes_dynamic(&mut BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &mut BigEndian, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<LittleEndian> for $pty {
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
            /// use bytes::{LittleEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(LittleEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x2A, 0x00 ]);
            /// 
            /// let mut buf: [u8; 1] = [0; 1];
            /// assert!(matches!(42u16.try_to_bytes_dynamic(LittleEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
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
        impl TryToBytesDynamic<&LittleEndian> for $pty {
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
            /// use bytes::{LittleEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(&LittleEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x2A, 0x00 ]);
            /// 
            /// let mut buf: [u8; 1] = [0; 1];
            /// assert!(matches!(42u16.try_to_bytes_dynamic(&LittleEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }
        impl TryToBytesDynamic<&mut LittleEndian> for $pty {
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
            /// use bytes::{LittleEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(&mut LittleEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [ 0x2A, 0x00 ]);
            /// 
            /// let mut buf: [u8; 1] = [0; 1];
            /// assert!(matches!(42u16.try_to_bytes_dynamic(&mut LittleEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: &mut LittleEndian, writer: impl Write) -> Result<(), Self::Error> {
                self.try_to_bytes_dynamic(*input, writer)
            }
        }        
    };
}

/// Implements [`TryToBytesDynamic`] for a tuple of the given size.
/// 
/// The size is denoted as a pair of typenames, .e.g,
/// ```ignore
/// // Implements for a tuple of length three
/// try_to_bytes_dynamic_tuple_impl!(T1, T2, T3);
/// ```
macro_rules! try_to_bytes_dynamic_tuple_impl {
    // Case for empty tuple (unit type)
    () => {
        impl TryToBytesDynamic<NoInput> for () {
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
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 0] = [];
            /// ().try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, []);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, _input: NoInput, _writer: impl Write) -> Result<(), Self::Error> {
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
            /// 
            /// # Example
            /// ```rust
            /// use bytes::TryToBytesDynamic as _;
            /// 
            /// let mut buf: [u8; 4] = [0; 4];
            /// ().try_to_bytes_dynamic(4, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0, 0, 0, 0]);
            /// 
            /// let mut buf: [u8; 3] = [0; 3];
            /// assert!(matches!(().try_to_bytes_dynamic(4, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: usize, mut writer: impl Write) -> Result<(), Self::Error> {
                match writer.write_all(&vec![ 0; input ]) {
                    Ok(_)    => Ok(()),
                    Err(err) => Err(Error::Write { err }),
                }
            }
        }
    };

    // Case for a single-element tuple
    (($fty:ident, $fin:ident, $ffi:tt)) => {
        impl<$fty: TryToBytesDynamic<$fin>, $fin> TryToBytesDynamic<$fin> for ($fty,)
        where
            $fty::Error: 'static,
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
            /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`Error::Field`].
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 2] = [0; 2];
            /// 42u16.try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A]);
            /// 
            /// let mut buf: [u8; 1] = [0; 1];
            /// assert!(matches!(42u16.try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: $fin, writer: impl Write) -> Result<(), Self::Error> {
                match self.$ffi.try_to_bytes_dynamic(input, writer) {
                    Ok(_)    => Ok(()),
                    Err(err) => Err(Error::Field { name: stringify!($ffi).into(), err: Box::new(err) }),
                }
            }
        }
    };

    // Case for more than one tuple
    (($fty:ident, $fin:ident, $ffi:tt), $(($tys:ident, $ins:ident, $fis:tt)),+) => {
        impl<$fty: TryToBytesDynamic<NoInput>, $($tys: TryToBytesDynamic<NoInput>),+> TryToBytesDynamic<NoInput> for ($fty, $($tys),+)
        where
            $fty::Error: 'static,
            $($tys::Error: 'static),+
        {
            type Error = Error;

            /// Serializes a tuple of inner values that take no dynamic input.
            /// 
            /// This overload allows [`TryToBytes`] to be derived for tuples that support it.
            /// 
            /// It is assumed these values are tightly packed, i.e., should be serialized directly one after another. To add in some space between each elements, write them as tuples with the null-type (i.e., `(T, ())`).
            /// 
            /// # Arguments
            /// - `input`: Nothing, since the inner tuples do not take input.
            /// - `writer`: The [`Write`]r to which the inner serializes write.
            /// 
            /// # Errors
            /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`Error::Field`].
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{NoInput, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 8] = [0; 8];
            /// 
            /// (42u8, 42u8).try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x2A, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u8, 42u8, 42u8).try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x2A, 0x2A, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u8, 42u8, 42u8, 42u8).try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x2A, 0x2A, 0x2A, 0x2A, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u8, 42u8, 42u8, 42u8, 42u8).try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x00, 0x00, 0x00]);
            /// 
            /// (42u8, 42u8, 42u8, 42u8, 42u8, 42u8).try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x00, 0x00]);
            /// 
            /// (42u8, 42u8, 42u8, 42u8, 42u8, 42u8, 42u8).try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x00]);
            /// 
            /// (42u8, 42u8, 42u8, 42u8, 42u8, 42u8, 42u8, 42u8).try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, _input: NoInput, mut writer: impl Write) -> Result<(), Self::Error> {
                // Simply serialize the fields one after another
                if let Err(err) = self.$ffi.try_to_bytes_dynamic(NoInput, &mut writer) {
                    return Err(Error::Field { name: stringify!($ffi).into(), err: Box::new(err) });
                }
                $(if let Err(err) = self.$fis.try_to_bytes_dynamic(NoInput, &mut writer) {
                    return Err(Error::Field { name: stringify!($fis).into(), err: Box::new(err) });
                })+
                Ok(())
            }
        }
        impl<$fty: TryToBytesDynamic<$fin>, $($tys: TryToBytesDynamic<$ins>),+, $fin, $($ins),+> TryToBytesDynamic<($fin, $($ins),+)> for ($fty, $($tys),+)
        where
            $fty::Error: 'static,
            $($tys::Error: 'static),+
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
            /// This function may error if any of the inner serializers error. If so, then the error is wrapped in a [`Error::Field`].
            /// 
            /// # Example
            /// ```rust
            /// use bytes::{BigEndian, TryToBytesDynamic as _};
            /// 
            /// let mut buf: [u8; 16] = [0; 16];
            /// 
            /// (42u16, 42u16).try_to_bytes_dynamic((BigEndian, BigEndian), &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A, 0x00, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u16, 42u16, 42u16).try_to_bytes_dynamic((BigEndian, BigEndian, BigEndian), &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u16, 42u16, 42u16, 42u16).try_to_bytes_dynamic((BigEndian, BigEndian, BigEndian, BigEndian), &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u16, 42u16, 42u16, 42u16, 42u16).try_to_bytes_dynamic((BigEndian, BigEndian, BigEndian, BigEndian, BigEndian), &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u16, 42u16, 42u16, 42u16, 42u16, 42u16).try_to_bytes_dynamic((BigEndian, BigEndian, BigEndian, BigEndian, BigEndian, BigEndian), &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x00, 0x00, 0x00]);
            /// 
            /// (42u16, 42u16, 42u16, 42u16, 42u16, 42u16, 42u16).try_to_bytes_dynamic((BigEndian, BigEndian, BigEndian, BigEndian, BigEndian, BigEndian, BigEndian), &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x00]);
            /// 
            /// (42u16, 42u16, 42u16, 42u16, 42u16, 42u16, 42u16, 42u16).try_to_bytes_dynamic((BigEndian, BigEndian, BigEndian, BigEndian, BigEndian, BigEndian, BigEndian, BigEndian), &mut buf[..]).unwrap();
            /// assert_eq!(buf, [0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A, 0x00, 0x2A]);
            /// ```
            #[inline]
            fn try_to_bytes_dynamic(&self, input: ($fin, $($ins),+), mut writer: impl Write) -> Result<(), Self::Error> {
                // Simply serialize the fields one after another
                if let Err(err) = self.$ffi.try_to_bytes_dynamic(input.$ffi, &mut writer) {
                    return Err(Error::Field { name: stringify!($ffi).into(), err: Box::new(err) });
                }
                $(if let Err(err) = self.$fis.try_to_bytes_dynamic(input.$fis, &mut writer) {
                    return Err(Error::Field { name: stringify!($fis).into(), err: Box::new(err) });
                })+
                Ok(())
            }
        }
    };
}





/***** ERRORS *****/
/// Defines errors that may occur when using library serializers.
/// 
/// Note that this struct is designed to report nested errors only when [`source()`](error::Error::source()()) is called.
/// As such, consider using a library for reporting these easily (e.g., <https://github.com/Lut99/error-trace-rs>).
#[derive(Debug)]
pub enum Error {
    /// Couldn't write to the given writer.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryToBytes as _;
    /// 
    /// let mut buf: [u8; 0] = [];
    /// assert!(matches!(0u8.try_to_bytes(&mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
    /// ```
    Write { err: std::io::Error },
    /// A sub-serializer of a field failed.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryToBytes;
    /// 
    /// #[derive(TryToBytes)]
    /// struct Example {
    ///     #[bytes]
    ///     field_1 : u32
    /// }
    /// 
    /// assert!(matches!(Example { field_1: 42 }.try_to_bytes(&mut [][..]), Err(bytes::to_bytes::Error::Field{ .. })));
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





/***** AUXILLARY *****/
/// Allows a type to be serialized to bytes.
/// 
/// This trait acts as an alias for [`TryToBytesDynamic`] in scenario's where no input is required (i.e., `()`).
/// As such, it is automatically implemented for that cases.
/// 
/// This can be automatically derived using the [`TryToBytes`](crate::procedural)-macro.
/// 
/// # Example
/// ```rust
/// use bytes::{BigEndian, TryToBytes};
/// 
/// #[derive(TryToBytes)]
/// struct Example {
///     #[bytes(input = BigEndian)]
///     num : u16,
/// }
/// 
/// let mut buf: [u8; 2] = [0; 2];
/// Example { num: 42 }.try_to_bytes(&mut buf[..]).unwrap();
/// assert_eq!(buf, [ 0x00, 0x2A ]);
/// ```
pub trait TryToBytes: TryToBytesDynamic<NoInput> {
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
    /// use bytes::{BigEndian, TryToBytes as _};
    /// 
    /// let mut buf: [u8; 0] = [];
    /// ().try_to_bytes(&mut buf[..]).unwrap();
    /// assert_eq!(buf, []);
    /// ```
    fn try_to_bytes(&self, writer: impl Write) -> Result<(), Self::Error>;

    /// Convenience function that writes to a vector.
    /// 
    /// # Returns
    /// A vector of bytes ([`Vec<u8>`]) that contains the serialized result.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the given bytes.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, TryToBytes as _};
    /// 
    /// assert_eq!("Hello, world!".try_to_bytes_vec().unwrap(), vec![ 0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x2C, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0x21 ]);
    /// ```
    #[inline]
    fn try_to_bytes_vec(&self) -> Result<Vec<u8>, Self::Error> {
        let mut res: Vec<u8> = vec![];
        self.try_to_bytes(&mut res)?;
        Ok(res)
    }
}
impl<T: ?Sized + TryToBytesDynamic<NoInput>> TryToBytes for T {
    /// Automatic implementation for types implementing [`TryToBytesDynamic`] but require no input (i.e., `()`).
    #[inline]
    fn try_to_bytes(&self, writer: impl Write) -> Result<(), Self::Error> {
        self.try_to_bytes_dynamic(NoInput, writer)
    }
}





/***** LIBRARY *****/
/// Allows a type to be serialized to bytes, using some additional input for configuration.
/// 
/// This can be automatically derived using the [`TryToBytesDynamic`](crate::procedural)-macro.
/// 
/// # Example
/// ```rust
/// use bytes::{Endianness, TryToBytesDynamic};
/// 
/// #[derive(TryToBytesDynamic)]
/// #[bytes(dynamic_ty = "Endianness")]
/// struct Example {
///     #[bytes(input = input)]
///     num : u16,
/// }
/// 
/// let mut buf: [u8; 2] = [0; 2];
/// Example { num: 42 }.try_to_bytes_dynamic(Endianness::Big, &mut buf[..]).unwrap();
/// assert_eq!(buf, [ 0x00, 0x2A ]);
/// Example { num: 42 }.try_to_bytes_dynamic(Endianness::Little, &mut buf[..]).unwrap();
/// assert_eq!(buf, [ 0x2A, 0x00 ]);
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
    /// use bytes::{BigEndian, TryToBytesDynamic};
    /// 
    /// let mut buf: [u8; 2] = [0; 2];
    /// 42u16.try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [ 0x00, 0x2A ]);
    /// ```
    fn try_to_bytes_dynamic(&self, input: I, writer: impl Write) -> Result<(), Self::Error>;

    /// Convenience function that writes to a vector.
    /// 
    /// # Arguments
    /// - `input`: The additional input needed to make sense of this, like some length.
    /// 
    /// # Returns
    /// A vector of bytes ([`Vec<u8>`]) that contains the serialized result.
    /// 
    /// # Errors
    /// This function may error if we failed to serialize the given bytes.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, TryToBytesDynamic as _};
    /// 
    /// assert_eq!(42u16.try_to_bytes_dynamic_vec(BigEndian).unwrap(), vec![ 0x00, 0x2A ]);
    /// ```
    #[inline]
    fn try_to_bytes_dynamic_vec(&self, input: I) -> Result<Vec<u8>, Self::Error> {
        let mut res: Vec<u8> = vec![];
        self.try_to_bytes_dynamic(input, &mut res)?;
        Ok(res)
    }
}

// Implement it for primitives
try_to_bytes_dynamic_primitive_impl!(u8);
try_to_bytes_dynamic_primitive_impl!(i8);
try_to_bytes_dynamic_primitive_impl!(u16);
try_to_bytes_dynamic_primitive_impl!(i16);
try_to_bytes_dynamic_primitive_impl!(u32);
try_to_bytes_dynamic_primitive_impl!(i32);
try_to_bytes_dynamic_primitive_impl!(u64);
try_to_bytes_dynamic_primitive_impl!(i64);
try_to_bytes_dynamic_primitive_impl!(u128);
try_to_bytes_dynamic_primitive_impl!(i128);
try_to_bytes_dynamic_primitive_impl!(usize);
try_to_bytes_dynamic_primitive_impl!(isize);
try_to_bytes_dynamic_primitive_impl!(f32);
try_to_bytes_dynamic_primitive_impl!(f64);
try_to_bytes_dynamic_primitive_impl!(char);

// Implement it for tightly-packed containers
try_to_bytes_dynamic_tuple_impl!();
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0));
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1));
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2));
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3));
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4));
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4), (T6, I6, 5));
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4), (T6, I6, 5), (T7, I7, 6));
try_to_bytes_dynamic_tuple_impl!((T1, I1, 0), (T2, I2, 1), (T3, I3, 2), (T4, I4, 3), (T5, I5, 4), (T6, I6, 5), (T7, I7, 6), (T8, I8, 7));
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
    /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`Error::Field`].
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 4] = [0; 4];
    /// [ 42u16, 42u16 ].try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [ 0x00, 0x2A, 0x00, 0x2A ]);
    /// 
    /// let mut buf: [u8; 3] = [0; 3];
    /// assert!(matches!([ 42u16, 42u16 ].try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Field { .. })));
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
    /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`Error::Field`].
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 4] = [0; 4];
    /// ([ 42u16, 42u16 ][..]).try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [ 0x00, 0x2A, 0x00, 0x2A ]);
    /// 
    /// let mut buf: [u8; 3] = [0; 3];
    /// assert!(matches!(([ 42u16, 42u16 ][..]).try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Field { .. })));
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
    /// This function may error if the inner serializer errors. If so, then the error is wrapped in a [`Error::Field`].
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 4] = [0; 4];
    /// vec![ 42u16, 42u16 ].try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [ 0x00, 0x2A, 0x00, 0x2A ]);
    /// 
    /// let mut buf: [u8; 3] = [0; 3];
    /// assert!(matches!(vec![ 42u16, 42u16 ].try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Field { .. })));
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
impl TryToBytesDynamic<NoInput> for str {
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
    /// use bytes::{NoInput, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 13] = [0; 13];
    /// "Hello, world!".try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x2C, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0x21]);
    /// 
    /// let mut buf: [u8; 12] = [0; 12];
    /// assert!(matches!("Hello, world!".try_to_bytes_dynamic(NoInput, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: NoInput, mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl TryToBytesDynamic<NoInput> for Cow<'_, str> {
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
    /// # use std::borrow::Cow;
    /// use bytes::{NoInput, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 13] = [0; 13];
    /// Cow::Borrowed("Hello, world!").try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x2C, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0x21]);
    /// 
    /// let mut buf: [u8; 12] = [0; 12];
    /// assert!(matches!(Cow::Borrowed("Hello, world!").try_to_bytes_dynamic(NoInput, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: NoInput, mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}
impl TryToBytesDynamic<NoInput> for String {
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
    /// use bytes::{NoInput, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 13] = [0; 13];
    /// "Hello, world!".to_string().try_to_bytes_dynamic(NoInput, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x2C, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0x21]);
    /// 
    /// let mut buf: [u8; 12] = [0; 12];
    /// assert!(matches!("Hello, world!".to_string().try_to_bytes_dynamic(NoInput, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, _input: NoInput, mut writer: impl Write) -> Result<(), Self::Error> {
        match writer.write_all(&self.as_bytes()) {
            Ok(_)    => Ok(()),
            Err(err) => Err(Error::Write { err }),
        }
    }
}

// Generalise over references
impl<T: TryToBytesDynamic<I>, I> TryToBytesDynamic<I> for &T {
    type Error = T::Error;

    /// Serializer for a reference to a type that is serializable.
    /// 
    /// # Arguments
    /// - `input`: The input to the type such that it may be serialized.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if the type's serializer errors.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 2] = [0; 2];
    /// (&42u16).try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [0x00, 0x2A]);
    /// 
    /// let mut buf: [u8; 1] = [0; 1];
    /// assert!(matches!((&42u16).try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: I, writer: impl Write) -> Result<(), Self::Error> {
        <T as TryToBytesDynamic<I>>::try_to_bytes_dynamic(*self, input, writer)
    }
}
impl<T: TryToBytesDynamic<I>, I> TryToBytesDynamic<I> for &mut T {
    type Error = T::Error;

    /// Serializer for a mutable reference to a type that is serializable.
    /// 
    /// # Arguments
    /// - `input`: The input to the type such that it may be serialized.
    /// - `writer`: The [`Write`]r to which we serialize.
    /// 
    /// # Errors
    /// This function may error if the type's serializer errors.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::{BigEndian, TryToBytesDynamic as _};
    /// 
    /// let mut buf: [u8; 2] = [0; 2];
    /// (&mut 42u16).try_to_bytes_dynamic(BigEndian, &mut buf[..]).unwrap();
    /// assert_eq!(buf, [0x00, 0x2A]);
    /// 
    /// let mut buf: [u8; 1] = [0; 1];
    /// assert!(matches!((&mut 42u16).try_to_bytes_dynamic(BigEndian, &mut buf[..]), Err(bytes::to_bytes::Error::Write { .. })));
    /// ```
    #[inline]
    fn try_to_bytes_dynamic(&self, input: I, writer: impl Write) -> Result<(), Self::Error> {
        <T as TryToBytesDynamic<I>>::try_to_bytes_dynamic(*self, input, writer)
    }
}
