//  STRINGS.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 17:34:25
//  Last edited:
//    20 Sep 2023, 18:20:44
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines parsing a string with a dynamic size.
// 

use bytes::{TryFromBytes, TryFromBytesDynamic};


/***** BYTE FORMATS *****/
/// Showcases dynamic parsing based on user
#[derive(TryFromBytesDynamic)]
#[bytes(dynamic = "usize")]
struct StringsManual {
    /// Parse some text
    #[bytes(dynamic = dynamic_input)]
    text : String,
}

/// Showcases dynamic parsing based on input
#[derive(TryFromBytes)]
struct Strings {
    /// First, we parse the number of bytes the string is long...
    #[bytes]
    n_bytes : u8,
    /// ...and then we parse the string with that
    #[bytes(dynamic = n_bytes as usize)]
    text    : String,
}





/***** ENTRYPOINT *****/
fn main() {
    // The first, more manual case
    let input: &[u8] = &[ 0x47, 0x65, 0x6e, 0x65, 0x72, 0x61, 0x6c, 0x20, 0x4b, 0x65, 0x6e, 0x6f, 0x62, 0x69, 0x21 ];
    let text: StringsManual = StringsManual::try_from_bytes_dynamic(15, input).unwrap();
    assert_eq!(text.text, "General Kenobi!");

    // The second, more dynamic case
    let input: &[u8] = &[ 13, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ];
    let text: Strings = Strings::try_from_bytes(input).unwrap();
    assert_eq!(text.text, "Hello, world!");
}
