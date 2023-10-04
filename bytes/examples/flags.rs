//  FLAGS.rs
//    by Lut99
// 
//  Created:
//    21 Sep 2023, 13:50:25
//  Last edited:
//    04 Oct 2023, 23:04:19
//  Auto updated?
//    Yes
// 
//  Description:
//!   Showcases parsing flags
// 

use bytes::{flags, Flags, TryFromBytes as _, TryToBytes as _};


/***** HEADERS *****/
// Defining our own type to name the flags!
flags! {
    /// Example struct that reads three successive bits from the input stream.
    /// 
    /// Note that the rest of the byte will be discarded (i.e., it always reads whole bytes)
    flags CoolFlags {
        is_cool : bool,
        is_kind : bool,
        is_dope : bool,
    },

    /// We can also define some longer flags area with unused flags by simply adding bogus fields
    flags SparseFlags {
        // This will be byte 1, bit 1
        prop1 : bool,
        // Ignored!
        _res  : bool,
        // This will be byte 2, bit 8
        prop2 : bool,
    },
}





/***** ENTRYPOINT *****/
fn main() {
    /* PARSING */
    // Parse unnamed flags!
    let input: &[u8] = &[ 0b10100000 ];
    let flags: Flags<3> = Flags::try_from_bytes(input).unwrap();
    assert_eq!(flags[0], true);
    assert_eq!(flags[1], false);
    assert_eq!(flags[2], true);

    // Parse named flags!
    let input: &[u8] = &[ 0b10100000 ];
    let flags: CoolFlags = CoolFlags::try_from_bytes(input).unwrap();
    assert_eq!(flags.is_cool, true);
    assert_eq!(flags.is_kind, false);
    assert_eq!(flags.is_dope, true);

    // Parse sparse flags!
    let flags: SparseFlags = SparseFlags::try_from_bytes(input).unwrap();
    assert_eq!(flags.prop1, true);
    assert_eq!(flags.prop2, true);

    /* SERIALIZING */
    // Serialize unnamed flags!
    let flags: Flags<3> = Flags([false, false, true]);
    let mut bytes: [u8; 1] = [0; 1];
    flags.try_to_bytes(&mut bytes[..]).unwrap();
    assert_eq!(bytes[0], 0b00100000);

    // Serialize named flags!
    let flags: CoolFlags = CoolFlags { is_cool: false, is_kind: false, is_dope: true };
    let mut bytes: [u8; 1] = [0; 1];
    flags.try_to_bytes(&mut bytes[..]).unwrap();
    assert_eq!(bytes[0], 0b00100000);

    // Serialize sparse flags!
    let flags: SparseFlags = SparseFlags { prop1: true, _res: false, prop2: false,  };
    let mut bytes: [u8; 1] = [0; 1];
    flags.try_to_bytes(&mut bytes[..]).unwrap();
    assert_eq!(bytes[0], 0b10000000);
}
