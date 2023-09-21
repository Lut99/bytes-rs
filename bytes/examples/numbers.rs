//  NUMBERS.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 13:44:24
//  Last edited:
//    21 Sep 2023, 13:40:08
//  Auto updated?
//    Yes
// 
//  Description:
//!   Shows deriving a struct using the provided numbers.
// 

use bytes::{BigEndian, LittleEndian, TryFromBytes};


/***** BYTE FORMATS *****/
#[derive(TryFromBytes)]
struct Numbers {
    /// Some number that will be parsed in big-endian format.
    #[bytes(dynamic = BigEndian)]
    first  : u32,
    /// Some smaller number that will be parsed in little-endian format.
    #[bytes(dynamic = LittleEndian)]
    second : u16,
}





/***** ENTRYPOINT *****/
fn main() {
    // Parse the bytes!
    let input: &[u8] = &[ 0x00, 0x00, 0x00, 0x2A, 0x2A, 0x00 ];
    let nums: Numbers = Numbers::try_from_bytes(input).unwrap();

    // Make some assertions about what we parsed
    assert_eq!(nums.first, 42);
    assert_eq!(nums.second, 42);
}
