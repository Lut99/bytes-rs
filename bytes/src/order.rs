//  ORDER.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 14:39:18
//  Last edited:
//    20 Sep 2023, 15:17:36
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines static structs allowing the use of specific ordering for
//!   parsers.
// 


/***** LIBRARY *****/
/// Abstracts over the various endiannesses.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Endianness {
    /// Represents little-endian ordering, i.e., MSB first.
    Little,
    /// Represents big-endian ordering, i.e., LSB first.
    Big,
}

/// Instructs a number parser to parse little-endian.
#[derive(Clone, Copy, Debug)]
pub struct LittleEndian;

/// Instructs a number parser to parse big-endian.
#[derive(Clone, Copy, Debug)]
pub struct BigEndian;
