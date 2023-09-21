//  LIB.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:05:57
//  Last edited:
//    21 Sep 2023, 12:34:35
//  Auto updated?
//    Yes
// 
//  Description:
//!   A package for easily defining header-like structs that can be parsed
//!   from bytes with static interpretation.
// 

// Declare the submodules
pub mod errors;
pub mod flags;
// pub mod num;
pub mod order;
pub mod spec;
pub mod string;



// Bring some of that into the crate namespace
pub use order::{BigEndian, Endianness, LittleEndian};
pub use spec::{ParsedLength, TryFromBytes, TryFromBytesDynamic};
pub use string::{Lossiness, Lossy, NonLossy};



// Pull any procedural macros into this namespace
/// This module documents the use of the various procedural macros defined in the [`bytes_derive`]-crate.
#[cfg(feature = "derive")]
pub mod procedural {
    #[allow(non_snake_case)]
    pub mod TryFromBytes {}



    #[allow(non_snake_case)]
    pub mod TryFromBytesDynamic {}
}
#[cfg(feature = "derive")]
pub use bytes_derive::{TryFromBytes, TryFromBytesDynamic};
