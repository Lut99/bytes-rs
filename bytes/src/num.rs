//  NUM.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:24:26
//  Last edited:
//    20 Sep 2023, 14:20:39
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines some new types over default rust numbers that differentiate
//!   between little endian and big endian and such.
// 

use std::mem::size_of;
use std::ops::{Deref, DerefMut};

use crate::spec::{ParsedLength, TryFromBytes};


/***** HELPER MACROS *****/
/// Implements the newtypes for a given numeric type.
macro_rules! num_impl {
    {
        $(#[$attrs:meta])*
        num $name:ident ( $num:ident ) <= $parser:ident;
    } => {
        $(#[$attrs])*
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub struct $name(pub $num);
        impl Default for $name {
            #[inline]
            fn default() -> Self { Self(Default::default()) }
        }
        impl TryFromBytes for $name {
            type Error = std::array::TryFromSliceError;

            #[inline]
            fn try_from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
                let mut bytes: &[u8] = bytes.as_ref();
                if bytes.len() > size_of::<$num>() { bytes = &bytes[..size_of::<$num>()]; }
                Ok(Self($num::$parser(bytes.try_into()?)))
            }
        }
        impl ParsedLength for $name {
            #[inline]
            fn parsed_len(&self) -> usize {
                size_of::<$num>()
            }
        }
        impl Deref for $name {
            type Target = $num;

            #[inline]
            fn deref(&self) -> &Self::Target { &self.0 }
        }
        impl DerefMut for $name {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
        }
        impl From<$num> for $name {
            #[inline]
            fn from(value: $num) -> Self { Self(value) }
        }
        impl From<$name> for $num {
            #[inline]
            fn from(value: $name) -> Self { value.0 }
        }
    };

    {
        $(#[$le_attrs:meta])*
        little_endian $le_name:ident ( $le_num:ident );

        $(#[$be_attrs:meta])*
        big_endian $be_name:ident ( $be_num:ident );
    } => {
        num_impl! {
            $(#[$le_attrs])*
            num $le_name ( $le_num ) <= from_le_bytes;
        }

        num_impl! {
            $(#[$be_attrs])*
            num $be_name ( $be_num ) <= from_be_bytes;
        }
    };
}





/***** LIBRARY *****/
num_impl! {
    /// Defines an 8-bit, unsigned integer that can be parsed from bytes.
    /// 
    /// # Example
    /// ```rust
    /// 
    /// ```
    #[allow(non_camel_case_types)]
    num u8(u8) <= from;
}

num_impl! {
    /// Defines a 16-bit, unsigned integer that is parsed as little-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::u16_le;
    /// 
    /// assert_eq!(*u16_le::try_from_bytes(&[ 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*u16_le::try_from_bytes(&[ 0x00, 0x2A ]).unwrap(), 10752);
    /// assert_eq!(*u16_le::try_from_bytes(&[ 0x2A, 0x00 ]).unwrap(), 42);
    /// assert_eq!(*u16_le::try_from_bytes(&[ 0x2A, 0x2A ]).unwrap(), 10794);
    /// assert!(u16_le::try_from_bytes(&[]).is_err());
    /// assert!(u16_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    little_endian u16_le(u16);

    /// Defines a 16-bit, unsigned integer that is parsed in big-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::u16_be;
    /// 
    /// assert_eq!(*u16_be::try_from_bytes(&[ 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*u16_be::try_from_bytes(&[ 0x00, 0x2A ]).unwrap(), 42);
    /// assert_eq!(*u16_be::try_from_bytes(&[ 0x2A, 0x00 ]).unwrap(), 10752);
    /// assert_eq!(*u16_be::try_from_bytes(&[ 0x2A, 0x2A ]).unwrap(), 10794);
    /// assert!(u16_be::try_from_bytes(&[]).is_err());
    /// assert!(u16_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    big_endian u16_be(u16);
}
num_impl! {
    /// Defines a 16-bit, signed integer that is parsed as little-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::i16_le;
    /// 
    /// assert_eq!(*i16_le::try_from_bytes(&[ 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*i16_le::try_from_bytes(&[ 0x00, 0xFF ]).unwrap(), -256);
    /// assert_eq!(*i16_le::try_from_bytes(&[ 0xFF, 0x00 ]).unwrap(), 255);
    /// assert_eq!(*i16_le::try_from_bytes(&[ 0xFF, 0xFF ]).unwrap(), -1);
    /// assert!(i16_le::try_from_bytes(&[]).is_err());
    /// assert!(i16_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    little_endian i16_le(i16);

    /// Defines a 16-bit, signed integer that is parsed in big-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::i16_be;
    /// 
    /// assert_eq!(*i16_be::try_from_bytes(&[ 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*i16_be::try_from_bytes(&[ 0x00, 0xFF ]).unwrap(), 255);
    /// assert_eq!(*i16_be::try_from_bytes(&[ 0xFF, 0x00 ]).unwrap(), -256);
    /// assert_eq!(*i16_be::try_from_bytes(&[ 0xFF, 0xFF ]).unwrap(), -1);
    /// assert!(i16_be::try_from_bytes(&[]).is_err());
    /// assert!(i16_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    big_endian i16_be(i16);
}

num_impl! {
    /// Defines a 32-bit, unsigned integer that is parsed as little-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::u32_le;
    /// 
    /// assert_eq!(*u32_le::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*u32_le::try_from_bytes(&[ 0x00, 0x00, 0x2A, 0x2A ]).unwrap(), 707395584);
    /// assert_eq!(*u32_le::try_from_bytes(&[ 0x2A, 0x2A, 0x00, 0x00 ]).unwrap(), 10794);
    /// assert_eq!(*u32_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).unwrap(), 707406378);
    /// assert!(u32_le::try_from_bytes(&[]).is_err());
    /// assert!(u32_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u32_le::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u32_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    little_endian u32_le(u32);

    /// Defines a 32-bit, unsigned integer that is parsed in big-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::u32_be;
    /// 
    /// assert_eq!(*u32_be::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*u32_be::try_from_bytes(&[ 0x00, 0x00, 0x2A, 0x2A ]).unwrap(), 10794);
    /// assert_eq!(*u32_be::try_from_bytes(&[ 0x2A, 0x2A, 0x00, 0x00 ]).unwrap(), 707395584);
    /// assert_eq!(*u32_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).unwrap(), 707406378);
    /// assert!(u32_be::try_from_bytes(&[]).is_err());
    /// assert!(u32_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u32_be::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u32_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    big_endian u32_be(u32);
}
num_impl! {
    /// Defines a 32-bit, signed integer that is parsed as little-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::i32_le;
    /// 
    /// assert_eq!(*i32_le::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*i32_le::try_from_bytes(&[ 0x00, 0x00, 0xFF, 0xFF ]).unwrap(), -65536);
    /// assert_eq!(*i32_le::try_from_bytes(&[ 0xFF, 0xFF, 0x00, 0x00 ]).unwrap(), 65535);
    /// assert_eq!(*i32_le::try_from_bytes(&[ 0xFF, 0xFF, 0xFF, 0xFF ]).unwrap(), -1);
    /// assert!(i32_le::try_from_bytes(&[]).is_err());
    /// assert!(i32_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(i32_le::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(i32_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    little_endian i32_le(i32);

    /// Defines a 32-bit, signed integer that is parsed in big-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::i32_be;
    /// 
    /// assert_eq!(*i32_be::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*i32_be::try_from_bytes(&[ 0x00, 0x00, 0xFF, 0xFF ]).unwrap(), 65535);
    /// assert_eq!(*i32_be::try_from_bytes(&[ 0xFF, 0xFF, 0x00, 0x00 ]).unwrap(), -65536);
    /// assert_eq!(*i32_be::try_from_bytes(&[ 0xFF, 0xFF, 0xFF, 0xFF ]).unwrap(), -1);
    /// assert!(i32_be::try_from_bytes(&[]).is_err());
    /// assert!(i32_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(i32_be::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(i32_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    big_endian i32_be(i32);
}

num_impl! {
    /// Defines a 64-bit, unsigned integer that is parsed as little-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::u64_le;
    /// 
    /// assert_eq!(*u64_le::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*u64_le::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0x2A, 0x2A, 0x2A, 0x2A ]).unwrap(), 3038287258491813888);
    /// assert_eq!(*u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 707406378);
    /// assert_eq!(*u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).unwrap(), 3038287259199220266);
    /// assert!(u64_le::try_from_bytes(&[]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    little_endian u64_le(u64);

    /// Defines a 64-bit, unsigned integer that is parsed in big-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::u64_be;
    /// 
    /// assert_eq!(*u64_be::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*u64_be::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0x2A, 0x2A, 0x2A, 0x2A ]).unwrap(), 707406378);
    /// assert_eq!(*u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 3038287258491813888);
    /// assert_eq!(*u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).unwrap(), 3038287259199220266);
    /// assert!(u64_be::try_from_bytes(&[]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    big_endian u64_be(u64);
}

num_impl! {
    /// Defines a 64-bit, signed integer that is parsed as little-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::i64_le;
    /// 
    /// assert_eq!(*i64_le::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*i64_le::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF ]).unwrap(), -4294967296);
    /// assert_eq!(*i64_le::try_from_bytes(&[ 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 4294967295);
    /// assert_eq!(*i64_le::try_from_bytes(&[ 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF ]).unwrap(), -1);
    /// assert!(i64_le::try_from_bytes(&[]).is_err());
    /// assert!(i64_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(i64_le::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(i64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    little_endian i64_le(i64);

    /// Defines a 64-bit, signed integer that is parsed in big-endian order.
    /// 
    /// # Example
    /// ```rust
    /// use bytes::TryFromBytes as _;
    /// use bytes::num::i64_be;
    /// 
    /// assert_eq!(*i64_be::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), 0);
    /// assert_eq!(*i64_be::try_from_bytes(&[ 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF ]).unwrap(), 4294967295);
    /// assert_eq!(*i64_be::try_from_bytes(&[ 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00 ]).unwrap(), -4294967296);
    /// assert_eq!(*i64_be::try_from_bytes(&[ 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF ]).unwrap(), -1);
    /// assert!(i64_be::try_from_bytes(&[]).is_err());
    /// assert!(i64_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(i64_be::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(i64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(i64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    #[allow(non_camel_case_types)]
    big_endian i64_be(i64);
}

