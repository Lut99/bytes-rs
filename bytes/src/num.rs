//  NUM.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:24:26
//  Last edited:
//    19 Sep 2023, 21:58:21
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines some new types over default rust numbers that differentiate
//!   between little endian and big endian and such.
// 

use std::ops::{Deref, DerefMut};

use crate::spec::TryFromBytes;


/***** HELPER MACROS *****/
/// Implements the newtypes for a given numeric type.
macro_rules! num_impl {
    {
        $(#[$le_attrs:meta])*
        little_endian $le_name:ident ( $le_num:ident );

        $(#[$be_attrs:meta])*
        big_endian $be_name:ident ( $be_num:ident );
    } => {
        $(#[$le_attrs])*
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub struct $le_name(pub $le_num);
        impl TryFromBytes for $le_name {
            type Error = std::array::TryFromSliceError;

            #[inline]
            fn try_from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
                Ok(Self($le_num::from_le_bytes(bytes.as_ref().try_into()?)))
            }
        }
        impl Deref for $le_name {
            type Target = $le_num;

            #[inline]
            fn deref(&self) -> &Self::Target { &self.0 }
        }
        impl DerefMut for $le_name {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
        }
        impl From<$le_num> for $le_name {
            #[inline]
            fn from(value: $le_num) -> Self { Self(value) }
        }
        impl From<$le_name> for $le_num {
            #[inline]
            fn from(value: $le_name) -> Self { value.0 }
        }
    
        $(#[$be_attrs])*
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub struct $be_name(pub $be_num);
        impl TryFromBytes for $be_name {
            type Error = std::array::TryFromSliceError;

            #[inline]
            fn try_from_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, Self::Error> {
                Ok(Self($be_num::from_be_bytes(bytes.as_ref().try_into()?)))
            }
        }
        impl Deref for $be_name {
            type Target = $be_num;

            #[inline]
            fn deref(&self) -> &Self::Target { &self.0 }
        }
        impl DerefMut for $be_name {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
        }
        impl From<$be_num> for $be_name {
            #[inline]
            fn from(value: $be_num) -> Self { Self(value) }
        }
        impl From<$be_name> for $be_num {
            #[inline]
            fn from(value: $be_name) -> Self { value.0 }
        }
    };
}





/***** LIBRARY *****/
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
    /// assert!(u16_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// ```
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
    /// assert!(u16_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// ```
    big_endian u16_be(u16);
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
    /// assert!(u32_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u32_le::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u32_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
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
    /// assert!(u32_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u32_be::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u32_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    big_endian u32_be(u32);
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
    /// assert!(u64_le::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_le::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
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
    /// assert!(u64_be::try_from_bytes(&[ 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// assert!(u64_be::try_from_bytes(&[ 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A, 0x2A ]).is_err());
    /// ```
    big_endian u64_be(u64);
}
