//  LIB.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:05:57
//  Last edited:
//    19 Sep 2023, 21:51:22
//  Auto updated?
//    Yes
// 
//  Description:
//!   A package for easily defining header-like structs that can be parsed
//!   from bytes with static interpretation.
// 

// Declare the submodules
pub mod num;
pub mod spec;

// Bring some of that into the crate namespace
pub use spec::TryFromBytes;
