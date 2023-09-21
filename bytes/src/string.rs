//  STRING.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 16:58:59
//  Last edited:
//    21 Sep 2023, 14:45:12
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines some auxillary types for working with string parsers.
// 


/***** LIBRARY *****/
/// Defines a type that allows one to dynamically choose between lossy and non-lossy.
/// 
/// This enum is meant to be given as dynamic input to dynamically switch
/// between lossiness parsing.
/// 
/// # Example
/// ```rust
/// # fn some_condition() -> bool { true }
/// use bytes::{Lossiness, Lossy, NonLossy, TryFromBytesDynamic};
/// 
/// #[derive(Debug, TryFromBytesDynamic)]
/// #[bytes(dynamic = "Lossiness")]
/// struct Text {
///     #[bytes(dynamic = dynamic_input)]
///     txt : String,
/// }
/// 
/// if some_condition() {
///     assert_eq!(Text::try_from_bytes_dynamic(Lossiness::Lossy(Lossy(13)), &[ 0x48, 0xFF, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ]).unwrap().txt, "H�llo, world!");
/// } else {
///     assert!(Text::try_from_bytes_dynamic(Lossiness::NonLossy(NonLossy(13)), &[ 0x48, 0xFF, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ]).is_err());
/// }
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Lossiness {
    /// It's lossy
    Lossy(Lossy),
    /// It's non-lossy
    NonLossy(NonLossy),
}

/// Defines that a string can be parsed lossy (i.e., represent non-UTF-8 characters still) and of a certain length.
/// 
/// This struct is meant to be given as dynamic input to statically force lossy parsing for strings.
/// 
/// # Example
/// ```rust
/// use bytes::{Lossy, TryFromBytes};
/// 
/// #[derive(Debug, TryFromBytes)]
/// struct Text {
///     #[bytes(dynamic = Lossy(13))]
///     txt : String,
/// }
/// 
/// assert_eq!(Text::try_from_bytes(&[ 0x48, 0xFF, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ]).unwrap().txt, "H�llo, world!");
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Lossy(pub usize);

/// Defines that a string must be parsed non-lossy (i.e., all UTF-8) and of a certain length.
/// 
/// This struct is meant to be given as dynamic input to statically force lossless parsing for strings.
/// 
/// # Example
/// ```rust
/// use bytes::{NonLossy, TryFromBytes};
/// 
/// #[derive(Debug, TryFromBytes)]
/// struct Text {
///     #[bytes(dynamic = NonLossy(13))]
///     txt : String,
/// }
/// 
/// assert!(Text::try_from_bytes(&[ 0x48, 0xFF, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ]).is_err());
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NonLossy(pub usize);
