//  SKIPPED.rs
//    by Lut99
// 
//  Created:
//    21 Sep 2023, 13:41:21
//  Last edited:
//    21 Sep 2023, 13:45:44
//  Auto updated?
//    Yes
// 
//  Description:
//!   Example showing not all fields in a header need to be parsed.
// 

use bytes::TryFromBytes;


/***** HEADERS *****/
#[derive(TryFromBytes)]
struct Empty {
    /// Not parsed, but default!
    num1 : i16,
    /// Not parsed, but default!
    num2 : u16,
}

#[derive(TryFromBytes)]
struct Partial {
    /// Yes parsed :)
    #[bytes]
    num1 : i16,
    /// Not parsed, but default!
    num2 : u16,
}





/***** ENTRYPOINT *****/
fn main() {
    let empty = Empty::try_from_bytes(&[ 0x00, 0x2A, 0x00, 0x2A ]).unwrap();
    assert_eq!(empty.num1, 0);
    assert_eq!(empty.num2, 0);

    let partial = Partial::try_from_bytes(&[ 0x00, 0x2A, 0x00, 0x2A ]).unwrap();
    assert_eq!(partial.num1, 10752);
    assert_eq!(partial.num2, 0);
}
