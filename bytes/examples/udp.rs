//  UDP.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 18:26:35
//  Last edited:
//    21 Sep 2023, 12:32:01
//  Auto updated?
//    Yes
// 
//  Description:
//!   Showcases defining the header for parsing UDP datagrams.
//!   
//!   Example headers taken from: <https://www.geeksforgeeks.org/examples-on-udp-header/>.
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
    #[bytes(dynamic = BigEndian)]
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
    assert_eq!(dg1.checksum, 57879);

    let dg2 = [ 0x04, 0x21, 0x00, 0x0B, 0x00, 0x2A, 0xE2, 0x17 ];
    let dg2 = UdpHeader::try_from_bytes(&dg2).unwrap();
    assert_eq!(dg2.src_port, 1057);
    assert_eq!(dg2.dst_port, 11);
    assert_eq!(dg2.length, 42);
    assert_eq!(dg2.checksum, 57879);

    let dg3 = [ 0x03, 0x61, 0x10, 0x1A, 0x10, 0x4C, 0x62, 0x42 ];
    let dg3 = UdpHeader::try_from_bytes(&dg3).unwrap();
    assert_eq!(dg3.src_port, 865);
    assert_eq!(dg3.dst_port, 4122);
    assert_eq!(dg3.length, 4172);
    assert_eq!(dg3.checksum, 25154);
}
