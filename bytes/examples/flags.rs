//  FLAGS.rs
//    by Lut99
// 
//  Created:
//    21 Sep 2023, 13:50:25
//  Last edited:
//    21 Sep 2023, 14:01:46
//  Auto updated?
//    Yes
// 
//  Description:
//!   Showcases parsing flags
// 

use bytes::{Flags, TryFromBytes as _};


/***** HEADERS *****/
/// Defines how to read three successive flags stored within a byte.
/// 
/// Note that implementing a [`Flags`] automatically derives [`TryFromBytes`](struct@bytes::TryFromBytes) for us!
struct CoolFlags {
    is_cool : bool,
    is_kind : bool,
    is_dope : bool,
}
impl Flags for CoolFlags {
    fn from_bits(bits: Vec<bool>) -> Self {
        // Unwrap the list of flags, which should be exactly three long
        assert_eq!(bits.len(), 3);
        Self {
            is_cool : bits[0],
            is_kind : bits[1],
            is_dope : bits[2],
        }
    }

    #[inline]
    fn flag_count() -> usize { 3 }
}

/// We can also define some longer flags area with unused flags
struct SparseFlags {
    // This will be byte 1, bit 1
    prop1 : bool,
    // This will be byte 2, bit 8
    prop2 : bool,
}
impl Flags for SparseFlags {
    fn from_bits(bits: Vec<bool>) -> Self {
        // Unwrap the list of flags, which should be exactly sixteen long...
        assert_eq!(bits.len(), 16);

        // ...but we use only the first and the last
        Self {
            prop1 : bits[0],
            prop2 : bits[15],
        }
    }

    // The trick: we request way too many flags...
    #[inline]
    fn flag_count() -> usize { 16 }
}





/***** ENTRYPOINT *****/
fn main() {
    // Parse some flags!
    let input: &[u8] = &[ 0b10100000 ];
    let flags: CoolFlags = CoolFlags::try_from_bytes(input).unwrap();
    assert_eq!(flags.is_cool, true);
    assert_eq!(flags.is_kind, false);
    assert_eq!(flags.is_dope, true);

    // Parse more flags!
    let input: &[u8] = &[ 0b10010100, 0b00111000 ];
    let flags: SparseFlags = SparseFlags::try_from_bytes(input).unwrap();
    assert_eq!(flags.prop1, true);
    assert_eq!(flags.prop2, false);
}
