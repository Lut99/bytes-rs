//  UDP.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 18:26:35
//  Last edited:
//    20 Sep 2023, 18:34:16
//  Auto updated?
//    Yes
// 
//  Description:
//!   Showcases defining the header for parsing UDP datagrams.
//!   
//!   Example headers taken from: <>.
// 

use bytes::{BigEndian, TryFromBytes};


/***** HEADERS *****/
/// Can parse UDP headers, based on the spec on <https://en.wikipedia.org/wiki/User_Datagram_Protocol#UDP_datagram_structure>.
#[derive(TryFromBytes)]
struct UdpHeader {
    /// The packet source port.
    #[bytes(dynamic = BigEndian)]
    src_port : u16,
    /// The packet destination port.
    #[bytes(dynamic = BigEndian)]
    dst_port : u16,
    /// The length of the packet, in bytes.
    #[bytes(dynamic = BigEndian)]
    length   : u16,
    /// A checksum for the datagram.
    #[bytes]
    checksum : u16,
}




/***** ENTRYPOINT *****/
fn main() {
    // Parse some packets!
    let dg1 = [ 0x06, 0x32, 0x00, 0x0D, 0x00, 0x1C, 0xE2, 0x17 ];
    let dg1 = UdpHeader::try_from_bytes(&dg1).unwrap();
    assert_eq!(dg1.src_port, 1586);
    assert_eq!(dg1.dst_port, 13);
    assert_eq!(dg1.length, 28);
    assert_eq!(dg1.checksum, 6114);

    let dg2 = [ 0x06, 0x32, 0x00, 0x0D, 0x00, 0x1C, 0xE2, 0x17 ];
    let dg2 = UdpHeader::try_from_bytes(&dg2).unwrap();
    assert_eq!(dg2.src_port, 1586);
    assert_eq!(dg2.dst_port, 13);
    assert_eq!(dg2.length, 28);
    assert_eq!(dg2.checksum, 6114);
}
