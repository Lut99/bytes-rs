# bytes-rs
Adds a Rust derive macro that can be used to easily parse & serialize header-like bytes that have specified order and interpretation.


## Usage
The main use-case of this crate is to define structs that parse & serialize tightly-packed fields from a string of bytes.

For example, consider implementing a parser (`TryFromBytes`) and serializer (`TryToBytes`) for the UDP header using this crate:
```rust
use bytes::{BigEndian, TryFromBytes, TryToBytes};

// See the spec from Wikipedia:
// <https://en.wikipedia.org/wiki/User_Datagram_Protocol#UDP_datagram_structure>
#[derive(TryFromBytes, TryToBytes)]
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
```

A main feature of the crate is that parser can take runtime information for customization. In the previous example, we used this to force the numbers to be parsed in big-endian byte order; but we can also be more dynamic and refer to previous fields:
```rust
use bytes::{TryFromBytes, TryToBytes};

#[derive(TryFromBytes, TryToBytes)]
struct Text {
    /// The length of the text we will be parsing
    #[bytes]
    len : usize,   // Note: in bytes
    /// And then the text itself, from UTF-8
    #[bytes(input = len)]
    txt : String,
}

let input: &[u8] = &[ 13, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ];
let text = Text::try_from_bytes(input).unwrap();
assert_eq!(text.txt, "Hello, world!");

let mut output: [u8; 14] = [0; 14];
text.try_to_bytes(&mut output[..]).unwrap();
assert_eq!(&output, input);
```

For more information on the derive macros, refer to the documentation of the crate (and then the `procedural` module). Other examples may be found in the [examples](./bytes/examples/) directory or as examples in the docstrings.


## Installation
To use this crate into one of your projects, simply add it to your `Cargo.toml` file:
```toml
bytes = { git = "https://github.com/Lut99/bytes-rs" }
```
Optionally, you can commit to a particular tag:
```toml
bytes = { git = "https://github.com/Lut99/bytes-rs", tag = "v2.0.0" }
```

To build this crate's documentation and open it, run:
```bash
cargo doc --all-features --no-deps --open
```
in the root of the repository.

### Features
The crate has the following features:
- `derive`: When given, imports the `bytes-derive`-crate which enables the procedural macros (_enabled by default_).


## Contribution
If you are interested in contributing in this project, feel free to raise [an issue](https://github.com/Lut99/bytes-rs/issues) or create [a pull request](https://github.com/Lut99/bytes-rs/pulls). Note that this is mainly a hobby project, so not all suggestions may be accepted no matter how good it is ;)


## License
This project is licensed under the GPLv3 license. See [LICENSE](./LICENSE) for more information.
