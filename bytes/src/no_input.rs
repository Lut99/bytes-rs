//  NO INPUT.rs
//    by Lut99
// 
//  Created:
//    09 Oct 2023, 16:21:43
//  Last edited:
//    09 Oct 2023, 16:39:53
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines a special [`NoInput`]-type which can be used to indicate
//!   that a particular parser or serializer does not take any input.
// 


/***** LIBRARY *****/
/// A special type that is used by the [`bytes`]-library to mark that a parser
/// or serializer does not use any input. As such,
/// [`TryFromBytes`](crate::from_bytes::TryFromBytes) and/or
/// [`TryToBytes`](crate::to_bytes::TryToBytes) may be derived.
/// 
/// You may wonder why `()` isn't used for this. This is because `()` does not
/// implement [`AsRef<()>`], and future crates may somehow implement a new
/// trait that replaces [`AsRef`] if we make it auto-implemented on [`AsRef`]
/// (since upstread crates may implement [`AsRef<()>`] for `()`)...
/// 
/// # Example
/// ```rust
/// # use std::io::Read;
/// use bytes::{NoInput, TryFromBytes as _, TryFromBytesDynamic};
/// 
/// struct Test {
///     byte : u8,
/// }
/// impl TryFromBytesDynamic<NoInput> for Test {
///     type Error = std::convert::Infallible;
/// 
///     fn try_from_bytes_dynamic(_input: NoInput, mut reader: impl Read) -> Result<Self, Self::Error> {
///         // Attempt to read the byte
///         let mut buf: [u8; 1] = [0; 1];
///         reader.read_exact(&mut buf).unwrap();
///         Ok(Self { byte: buf[0] })
///     }
/// }
/// 
/// // We can now also use `try_from_bytes()`!
/// assert_eq!(Test::try_from_bytes(&[ 0x2A ][..]).unwrap().byte, 42);
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NoInput;
impl Default for NoInput {
    #[inline]
    fn default() -> Self { Self }
}
impl AsRef<NoInput> for NoInput {
    #[inline]
    fn as_ref(&self) -> &Self { self }
}
impl AsMut<NoInput> for NoInput {
    #[inline]
    fn as_mut(&mut self) -> &mut Self { self }
}
impl From<&NoInput> for NoInput {
    #[inline]
    fn from(value: &NoInput) -> Self { *value }
}
impl From<&mut NoInput> for NoInput {
    #[inline]
    fn from(value: &mut NoInput) -> Self { *value }
}
