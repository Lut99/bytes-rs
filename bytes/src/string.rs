//  STRING.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 16:58:59
//  Last edited:
//    20 Sep 2023, 17:06:06
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines some auxillary types for working with string parsers.
// 


/***** LIBRARY *****/
/// Defines a type that allows one to dynamically choose between lossy and non-lossy.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Lossiness {
    /// It's lossy
    Lossy(Lossy),
    /// It's non-lossy
    NonLossy(NonLossy),
}

/// Defines that a string can be parsed lossy (i.e., represent non-UTF-8 characters still) and of a certain length.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Lossy(pub usize);

/// Defines that a string must be parsed non-lossy (i.e., all UTF-8) and of a certain length.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NonLossy(pub usize);
