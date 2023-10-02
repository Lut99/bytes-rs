//  LIB.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:05:57
//  Last edited:
//    02 Oct 2023, 20:50:32
//  Auto updated?
//    Yes
// 
//  Description:
//!   Adds a Rust derive macro that can be used to easily parse header-like bytes that have specified order and interpretation.
//!   
//!   # Usage
//!   The main use-case of this crate is to define structs that parse tightly-packed fields from a string of bytes.
//!   
//!   For example, consider implementing a parser for the UDP header using this crate:
//!   ```rust
//!   use bytes::{BigEndian, TryFromBytes};
//!   
//!   // See the spec from Wikipedia:
//!   // <https://en.wikipedia.org/wiki/User_Datagram_Protocol#UDP_datagram_structure>
//!   #[derive(TryFromBytes)]
//!   struct UdpHeader {
//!       /// The packet source port.
//!       #[bytes(dynamic = BigEndian)]
//!       src_port : u16,
//!       /// The packet destination port.
//!       #[bytes(dynamic = BigEndian)]
//!       dst_port : u16,
//!       /// The length of the packet, in bytes.
//!       #[bytes(dynamic = BigEndian)]
//!       length   : u16,
//!       /// A checksum for the datagram.
//!       #[bytes(dynamic = BigEndian)]
//!       checksum : u16,
//!   }
//!   ```
//!   
//!   A main feature of the crate is that parser can take runtime information for customization. In the previous example, we used this to force the numbers to be parsed in big-endian byte order; but we can also be more dynamic and refer to previous fields:
//!   ```rust
//!   use bytes::TryFromBytes;
//!   
//!   #[derive(TryFromBytes)]
//!   struct Text {
//!       /// The length of the text we will be parsing
//!       #[bytes]
//!       len : usize,   // Note: in bytes
//!       /// And then the text itself, from UTF-8
//!       #[bytes(dynamic = len)]
//!       txt : String,
//!   }
//!   
//!   let input: &[u8] = &[ 13, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21 ];
//!   assert_eq!(Text::try_from_bytes(input).txt, "Hello, world!");
//!   ```
//!   
//!   For more information on the derive macros, refer to the documentation of the crate (and then the `procedural` module). Other examples may be found in the [examples](./bytes/examples/) directory or as examples in the docstrings.
//!   
//!   # Installation
//!   To use this crate into one of your projects, simply add it to your `Cargo.toml` file:
//!   ```toml
//!   bytes = { git = "https://github.com/Lut99/bytes-rs" }
//!   ```
//!   Optionally, you can commit to a particular tag:
//!   ```toml
//!   bytes = { git = "https://github.com/Lut99/bytes-rs", tag = "v1.0.0" }
//!   ```
//!   
//!   To build this crate's documentation and open it, run:
//!   ```bash
//!   cargo doc --all-features --no-deps --open
//!   ```
//!   in the root of the repository.
//!   
//!   ## Features
//!   The crate has the following features:
//!   - `derive`: When given, imports the `bytes-derive`-crate which enables the procedural macros (_enabled by default_).
//  

// Declare the submodules
// pub mod flags;
pub mod from_bytes;
pub mod order;
pub mod string;
pub mod to_bytes;



// Bring some of that into the crate namespace
// pub use flags::Flags;
pub use from_bytes::{TryFromBytes, TryFromBytesDynamic};
pub use order::{BigEndian, Endianness, LittleEndian};
pub use string::{Lossiness, Lossy, NonLossy};
pub use to_bytes::{TryToBytes, TryToBytesDynamic};



// Pull any procedural macros into this namespace
/// This module documents the use of the various procedural macros defined in the [`bytes_derive`]-crate.
#[cfg(feature = "derive")]
pub mod procedural {
    /// Defines a procedural macro for deriving [`TryFromBytes`](struct@crate::TryFromBytes)
    /// implementations on structs.
    /// 
    /// This is mostly useful for defining certain static byte layouts and how to parse them. For
    /// example:
    /// ```rust
    /// use bytes::{BigEndian, TryFromBytes};
    /// 
    /// #[derive(TryFromBytes)]
    /// struct UdpHeader {
    ///     /// The packet source port.
    ///     #[bytes(dynamic = BigEndian)]
    ///     src_port : u16,
    ///     /// The packet destination port.
    ///     #[bytes(dynamic = BigEndian)]
    ///     dst_port : u16,
    ///     /// The length of the packet, in bytes.
    ///     #[bytes(dynamic = BigEndian)]
    ///     length   : u16,
    ///     /// A checksum for the datagram.
    ///     #[bytes(dynamic = BigEndian)]
    ///     checksum : u16,
    /// }
    /// ```
    /// 
    /// Note that this trait is a shorthand for a
    /// [`TryFromBytesDynamic<()>`](struct@crate::TryFromBytesDynamic<()>), which implies a dynamic
    /// struct without input. As such, the derivation procedure for the two is exactly the same,
    /// except that the toplevel has no `#[bytes(dynamic = ...]` and `#[bytes(dynamic_name = ...]`
    /// fields (but the individual fields still do).
    /// 
    /// As such, we recommend you read the
    /// [`TryFromBytesDynamic`](crate::procedural::TryFromBytesDynamic)-macro documentation instead.
    #[allow(non_snake_case)]
    pub mod TryFromBytes {}



    /// Defines a procedural macro for deriving
    /// [`TryFromBytesDynamic`](struct@crate::TryFromBytesDynamic) implementations on structs.
    /// 
    /// This is mostly useful for defining certain static byte layouts and how to parse them. For
    /// example:
    /// ```rust
    /// use bytes::{BigEndian, TryFromBytesDynamic};
    /// 
    /// #[derive(TryFromBytesDynamic)]
    /// struct UdpHeader {
    ///     /// The packet source port.
    ///     #[bytes(dynamic = BigEndian)]
    ///     src_port : u16,
    ///     /// The packet destination port.
    ///     #[bytes(dynamic = BigEndian)]
    ///     dst_port : u16,
    ///     /// The length of the packet, in bytes.
    ///     #[bytes(dynamic = BigEndian)]
    ///     length   : u16,
    ///     /// A checksum for the datagram.
    ///     #[bytes(dynamic = BigEndian)]
    ///     checksum : u16,
    /// }
    /// ```
    /// 
    /// By default, it assumes that headers are tighly-packed series of bytes with special
    /// interpretation. As such, one can define a struct in terms of types that already implement
    /// [`TryFromBytesDynamic`](struct@crate::TryFromBytesDynamic) (or
    /// [`TryFromBytes`](struct@crate::TryFromBytes)).
    /// 
    /// 
    /// ## General usage
    /// Using the [`TryFromBytesDynamic](derive@crate::TryFromBytesDynamic) macro is as simple as
    /// adding it the derivation rules of a struct:
    /// ```rust
    /// # use bytes::TryFromBytesDynamic;
    /// #[derive(TryFromBytesDynamic)]
    /// struct Test {
    ///     
    /// }
    /// ```
    /// While this compiles, it uses a default input type of [`()`](core::primitive::unit). This
    /// input type is given as an additional parameter to
    /// [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic()) to be
    /// able to dynamically configure the parsing process. But since using the unit-type means that
    /// no input is needed, this is equivalent to [`TryFromBytes`](crate::procedural::TryFromBytes);
    /// and thus, we will explicitly add another input type by specifiying the `#[bytes(...)]`
    /// attribute on the toplevel struct:
    /// ```rust
    /// # use bytes::TryFromBytesDynamic;
    /// #[derive(TryFromBytesDynamic)]
    /// #[bytes(dynamic = "usize")]
    /// struct Test {
    ///     
    /// }
    /// ```
    /// 
    /// Then, we can add fields to our struct:
    /// ```rust
    /// # use bytes::TryFromBytesDynamic;
    /// #[derive(TryFromBytesDynamic)]
    /// #[bytes(dynamic = "usize")]
    /// struct Test {
    ///     /// Some initial number that is a byte
    ///     num  : u8,
    ///     /// A string value we parse next.
    ///     text : String,
    /// }
    /// ```
    /// However, this will not cause the parser to parse the given numbers, because we haven't
    /// annotated them as being sourced in bytes. As such, if we were to call
    /// [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic()), the
    /// [`Default`]-implementations of the types are called instead.
    /// 
    /// To fix this, we annotate the fields with additional `#[bytes]`-attributes:
    /// ```ignore
    /// # use bytes::TryFromBytesDynamic;
    /// #[derive(TryFromBytesDynamic)]
    /// #[bytes(dynamic = "usize")]
    /// struct Test {
    ///     /// Some initial number that is a byte
    ///     #[bytes]
    ///     num  : u8,
    ///     /// A string value we parse next.
    ///     #[bytes]
    ///     text : String,
    /// }
    /// ```
    /// However, this will also not compile! This is because we use the [`String`]-type, which is
    /// also implemented as a [`TryFromBytesDynamic`](struct@crate::TryFromBytesDynamic) and
    /// requires the number of bytes it should interpret as a string. Thus, we can also give the
    /// `dynamic = ...` attribute here. However, note that now we don't specify an input _type_,
    /// but an input _value_. And we can do so using any expression, including previously parsed
    /// fields!
    /// ```rust
    /// # use bytes::TryFromBytesDynamic;
    /// #[derive(TryFromBytesDynamic)]
    /// #[bytes(dynamic = "usize")]
    /// struct Test {
    ///     /// Some initial number that is a byte
    ///     #[bytes]
    ///     num  : u8,
    ///     /// A string value we parse next.
    ///     #[bytes(dynamic = num as usize)]
    ///     text : String,
    /// }
    /// ```
    /// This wil first parse a byte number, and then parse that many bytes as UTF-8 text.
    /// 
    /// However, note that we also require a usize input to our struct to parse. We can also use
    /// this, by using the `dynamic_input`-variable (default name):
    /// ```rust
    /// # use bytes::TryFromBytesDynamic;
    /// #[derive(TryFromBytesDynamic)]
    /// #[bytes(dynamic = "usize")]
    /// struct Test {
    ///     /// Some initial number that is a byte
    ///     #[bytes]
    ///     num  : u8,
    ///     /// A string value we parse next.
    ///     #[bytes(dynamic = dynamic_input)]
    ///     text : String,
    /// }
    /// ```
    /// Now, this struct will parse a single-byte number followed by a dynamically-determined
    /// number of UTF-8 bytes!
    /// 
    /// 
    /// ## Attributes
    /// To customize the behaviour of the derivation process, a number of toplevel- and field-level
    /// attributes are defined as arguments to the `#[bytes(...)]`-attribute.
    /// 
    /// ### Toplevel attributes
    /// - `#[bytes(dynamic = "<TYPE>")]`: Defines the type of the input in
    ///   [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic()). Note
    ///   that using a type of [`()`](core::primitive::unit) automatically derives
    ///   [`TryFromBytes`](struct@crate::TryFromBytes) because it is assumed that it means no input
    ///   is required. Default: `"()"`.
    /// 
    ///   **Example**:
    ///   ```rust
    ///   # use bytes::TryFromBytesDynamic;
    ///   #[derive(TryFromBytesDynamic)]
    ///   #[bytes(dynamic = "usize")]
    ///   struct Example {
    ///       // We can pass this to field parsers
    ///       #[bytes(dynamic = dynamic_input)]
    ///       text : String,
    ///   }
    ///   ```
    /// - `#[bytes(dynamic_name = "<NAME>")]`: Changes the name of the dynamic input variable in
    ///   the struct's parser (i.e., the name of the input-argument in
    ///   [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic())).
    ///   Only has effect when `#[bytes(dynamic = ...)]` is given. Default: `"dynamic_input"`.
    ///   
    ///   **Example**:
    ///   ```rust
    ///   # use bytes::TryFromBytesDynamic;
    ///   #[derive(TryFromBytesDynamic)]
    ///   #[bytes(dynamic = "usize", dynamic_name = "foo")]
    ///   struct Example {
    ///       // Now we can pass it as follows
    ///       #[bytes(dynamic = foo)]
    ///       text : String,
    ///   }
    ///   ```
    /// - `#[bytes(input_name = "<NAME>")]`: Changes the name of the variable that represents the
    ///   raw input bytestring during parsing (i.e., the name of the bytes-argument in
    ///   [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic())).
    ///   Default: `"bytes"`.
    ///   
    ///   **Example**:
    ///   ```rust
    ///   # use bytes::TryFromBytesDynamic;
    ///   #[derive(TryFromBytesDynamic)]
    ///   #[bytes(input_name = "input")]
    ///   struct Example {
    ///       /// Without the renaming, this would cause weird errors.
    ///       #[bytes]
    ///       bytes : [ u8; 10 ],
    ///   }
    ///   ```
    /// 
    /// ### Field-level attributes
    /// - `#[bytes(dynamic = <EXPR>)]`: Defines that the field uses
    ///   [`TryFromBytesDynamic`](struct@crate::TryFromBytesDynamic) instead of
    ///   [`TryFromBytes`](struct@crate::TryFromBytes) to provide the internal parser, and then
    ///   states the expression passed as the dynamic input. Note that this expression can include
    ///   the dynamic input value of the main struct as well as any _previous_ fields in the struct
    ///   declaration. If you need out-of-order parsing, then consider using
    ///   `#[bytes(offset = ...)]`.
    ///   
    ///   **Example**:
    ///   ```rust
    ///   # use bytes::TryFromBytesDynamic;
    ///   #[derive(TryFromBytesDynamic)]
    ///   struct Example {
    ///       /// We parse the length of the string first...
    ///       #[bytes]
    ///       len : usize,
    ///       /// ...and then parse that many + 5 bytes as string
    ///       #[bytes(dynamic = len + 5)]
    ///       txt : String,
    ///   }
    ///   ```
    /// - `#[bytes(offset = <NUM>)]`: Defines the offset of this field from the start of the raw
    ///   bytes given. This allows one to define fields out-of-order or to skip a bunch of useless
    ///   bytes. If omitted, then an offset immediately following the previous field is assumed.  
    ///   Note that this influences how other fields are passed, since the default offset is based
    ///   on the previous field.
    ///   
    ///   **Example**:
    ///   ```rust
    ///   # use bytes::TryFromBytesDynamic;
    ///   #[derive(TryFromBytesDynamic)]
    ///   struct Example {
    ///       // Psych, reverse order!
    ///       #[bytes(offset = 4)]
    ///       num2 : i32,
    ///       #[bytes(offset = 0)]
    ///       num1 : i32,
    ///   }
    ///   ```
    /// - `#[bytes(length = <NUM>)]`: Defines the length of bytes that this field consumed. This
    ///   is only used for computing the offset of the next field when it uses the default offset.
    ///   If omitted, then the current field's [`ParsedLength`](crate::ParsedLength) implementation
    ///   is used to determine it once it has been parsed.
    ///   
    ///   **Example**:
    ///   ```rust
    ///   # use bytes::TryFromBytesDynamic;
    ///   #[derive(TryFromBytesDynamic)]
    ///   struct Example {
    ///       // Imagine this field is followed by 4 garbage bytes; the first four bytes are
    ///       // parsed as a number, and then the rest is skipped before `num2` is parsed.
    ///       #[bytes(length = 8)]
    ///       num1 : i32,
    ///       #[bytes]
    ///       num2 : i32,
    ///   }
    ///   ```
    #[allow(non_snake_case)]
    pub mod TryFromBytesDynamic {}
}
#[cfg(feature = "derive")]
pub use bytes_derive::{TryFromBytes, TryFromBytesDynamic, TryToBytes, TryToBytesDynamic};
