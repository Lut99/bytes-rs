//  LIB.rs
//    by Lut99
// 
//  Created:
//    19 Sep 2023, 21:05:57
//  Last edited:
//    11 Oct 2023, 21:48:17
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
//!       #[bytes(input = BigEndian)]
//!       src_port : u16,
//!       /// The packet destination port.
//!       #[bytes(input = BigEndian)]
//!       dst_port : u16,
//!       /// The length of the packet, in bytes.
//!       #[bytes(input = BigEndian)]
//!       length   : u16,
//!       /// A checksum for the datagram.
//!       #[bytes(input = BigEndian)]
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
//!       len : u8,     // Note: length in number of bytes, not characters
//!       /// And then the text itself, from UTF-8
//!       #[bytes(input = len as usize)]
//!       txt : String,
//!   }
//!   
//!   let input: [u8; 14] = [ 13, 0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x2C, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0x21 ];
//!   assert_eq!(Text::try_from_bytes(&input[..]).unwrap().txt, "Hello, world!");
//!   ```
//! 
//!   Existing structs can also be serialized back:
//!   ```rust
//!   # use bytes::BigEndian;
//!   use bytes::TryToBytes;
//!   
//!   #[derive(TryToBytes)]
//!   // See definition above
//!   struct UdpHeader {
//!       // ...
//!   #     #[bytes(input = BigEndian)]
//!   #     src_port : u16,
//!   #     #[bytes(input = BigEndian)]
//!   #     dst_port : u16,
//!   #     #[bytes(input = BigEndian)]
//!   #     length   : u16,
//!   #     #[bytes(input = BigEndian)]
//!   #     checksum : u16,
//!   }
//!   
//!   let mut output: [u8; 8] = [0; 8];
//!   UdpHeader {
//!       src_port : 1586,
//!       dst_port : 13,
//!       length : 28,
//!       checksum : 57879,
//!   }.try_to_bytes(&mut output[..]).unwrap();
//!   assert_eq!(output, [ 0x06, 0x32, 0x00, 0x0D, 0x00, 0x1C, 0xE2, 0x17 ]);
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
//!   bytes = { git = "https://github.com/Lut99/bytes-rs", tag = "v2.0.0" }
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
pub mod flags;
pub mod from_bytes;
pub mod no_input;
pub mod order;
pub mod string;
pub mod to_bytes;



// Bring some of that into the crate namespace
pub use flags::Flags;
pub use from_bytes::{TryFromBytes, TryFromBytesDynamic};
pub use no_input::NoInput;
pub use order::{BigEndian, Endianness, LittleEndian};
pub use string::{Lossiness, Lossy, NonLossy};
pub use to_bytes::{TryToBytes, TryToBytesDynamic};



// Pull any procedural macros into this namespace
/// Documents procedural macros for deriving
/// [`TryToBytes`](trait@crate::TryToBytes),
/// [`TryToBytesDynamic`](trait@crate::TryToBytesDynamic),
/// [`TryFromBytes`](trait@crate::TryFromBytes) and
/// [`TryFromBytesDynamic`](trait@crate::TryFromBytesDynamic) implementations on structs.
/// 
/// This is mostly useful for defining certain static byte layouts and how to parse them. For
/// example:
/// ```rust
/// use bytes::{BigEndian, TryToBytes, TryFromBytes};
/// 
/// #[derive(TryFromBytes, TryToBytes)]
/// struct UdpHeader {
///     /// The packet source port.
///     #[bytes(input = BigEndian)]
///     src_port : u16,
///     /// The packet destination port.
///     #[bytes(input = BigEndian)]
///     dst_port : u16,
///     /// The length of the packet, in bytes.
///     #[bytes(input = BigEndian)]
///     length   : u16,
///     /// A checksum for the datagram.
///     #[bytes(input = BigEndian)]
///     checksum : u16,
/// }
/// ```
/// 
/// By default, it assumes that headers are tighly-packed series of bytes with special
/// interpretation. As such, one can define a struct in terms of types that already implement
/// [`TryFromBytesDynamic`](trait@crate::TryFromBytesDynamic) or
/// [`TryToBytesDynamic`](trait@crate::TryToBytesDynamic).
/// 
/// 
/// ## General usage
/// Using all four macros is extremely similar, so we explain the usage of the
/// [`TryFromBytesDynamic](derive@crate::TryFromBytesDynamic)-macro which can be generalised to
/// the other macro's.
/// 
/// Using the [`TryFromBytesDynamic](derive@crate::TryFromBytesDynamic) macro is as simple as
/// adding it the derivation rules of a struct:
/// ```rust
/// # use bytes::TryFromBytesDynamic;
/// #[derive(TryFromBytesDynamic)]
/// struct Test {
///     
/// }
/// ```
/// While this compiles, it uses a default input type of [`NoInput`](crate::no_input::NoInput).
/// This input type is given as an additional parameter to
/// [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic()) to be
/// able to dynamically configure the parsing process. But since using this special type means that
/// no input is needed, this is equivalent to [`TryFromBytes`](crate::procedural);
/// and thus, we will explicitly add another input type by specifiying the `#[bytes(...)]`
/// attribute on the toplevel struct:
/// ```rust
/// # use bytes::TryFromBytesDynamic;
/// #[derive(TryFromBytesDynamic)]
/// #[bytes(dynamic_ty = "usize")]
/// struct Test {
///     
/// }
/// ```
/// 
/// Then, we can add fields to our struct:
/// ```rust
/// # use bytes::TryFromBytesDynamic;
/// #[derive(TryFromBytesDynamic)]
/// #[bytes(dynamic_ty = "usize")]
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
/// #[bytes(dynamic_ty = "usize")]
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
/// also implemented as a [`TryFromBytesDynamic`](trait@crate::TryFromBytesDynamic) and
/// requires the number of bytes it should interpret as a string. Thus, we can give the
/// `input = ...` attribute here. However, note that now we don't specify an input _type_,
/// but an input _value_. And we can do so using any expression, including previously parsed
/// fields!
/// ```rust
/// # use bytes::TryFromBytesDynamic;
/// #[derive(TryFromBytesDynamic)]
/// #[bytes(dynamic_ty = "usize")]
/// struct Test {
///     /// Some initial number that is a byte
///     #[bytes]
///     num  : u8,
///     /// A string value we parse next.
///     #[bytes(input = num as usize)]
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
/// #[bytes(dynamic_ty = "usize")]
/// struct Test {
///     /// Some initial number that is a byte
///     #[bytes]
///     num  : u8,
///     /// A string value we parse next.
///     #[bytes(input = input)]
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
/// ### Global attributes
/// - `#[bytes(from(...))]` or `#[bytes(parse(...))]` or `#[bytes(parser(...))]`: Specifies a
///   "namespace" for other attributes that can be given. This can be read as: "Any attribute
///   in the `from`-namespace is only read by the parser." This allows you to give attributes
///   to only the parser, not the serializer.
///   
///   **Example**:
///   ```rust
///   # use bytes::{TryFromBytesDynamic, TryToBytesDynamic};
///   #[derive(TryFromBytesDynamic, TryToBytesDynamic)]
///   #[bytes(from(dynamic_ty = "usize"))]
///   struct Example {
///       // Now we can pass the `input` only when we're parsing, not when serializing!
///       #[bytes(from(input = input))]
///       text : String,
///   }
///   ```
/// - `#[bytes(to(...))]` or `#[bytes(serialize(...))]` or `#[bytes(serializer(...))]`: Specifies a
///   "namespace" for other attributes that can be given. This can be read as: "Any attribute
///   in the `to`-namespace is only read by the serializer." This allows you to give attributes
///   to only the serializer, not the parser.
///   
///   **Example**:
///   ```rust
///   # use bytes::{LittleEndian, TryFromBytes, TryToBytes};
///   #[derive(TryFromBytes, TryToBytes)]
///   struct Example {
///       // We only define a particular endianness for serializing; otherwise, use the native one
///       #[bytes(to(input = LittleEndian))]
///       num : u32,
///   }
///   ```
/// 
/// ### Toplevel attributes
/// - `#[bytes(dynamic_name = "<NAME>")]`: Changes the name of the dynamic input variable in
///   the struct's parser (i.e., the name of the input-argument in
///   [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic())).
///   Default: `"input"`.
///   
///   **Example**:
///   ```rust
///   # use bytes::TryFromBytesDynamic;
///   #[derive(TryFromBytesDynamic)]
///   #[bytes(dynamic_ty = "usize", dynamic_name = "foo")]
///   struct Example {
///       // Now we can pass it as follows
///       #[bytes(input = foo)]
///       text : String,
///   }
///   ```
/// - `#[bytes(dynamic_ty = "<TYPE>")]`: Defines the type of the input in
///   [`try_from_bytes_dynamic()`](crate::TryFromBytesDynamic::try_from_bytes_dynamic()). Note
///   that using a type of [`NoInput`](crate::no_input::NoInput) automatically derives
///   [`TryFromBytes`](trait@crate::TryFromBytes) because it is assumed that it means no input
///   is required. Default: `"NoInput"`.
/// 
///   **Example**:
///   ```rust
///   # use bytes::TryFromBytesDynamic;
///   #[derive(TryFromBytesDynamic)]
///   #[bytes(dynamic_ty = "usize")]
///   struct Example {
///       // We can pass this to field parsers
///       #[bytes(input = input)]
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
///   #[bytes(input_name = "foo")]
///   struct Example {
///       /// Without the renaming, this would cause weird errors.
///       #[bytes]
///       reader : [ u8; 10 ],
///   }
///   ```
/// - `#[bytes(generate_refs = <true|false>)]`: Determines whether to generate the "reference
///   implementation", i.e., implementations for a reference of the input type. This is
///   typically desired for compatability with the library array/vector parser/serializer, and
///   should only be disabled if your input type does not implement [`Clone`] or there's a more
///   efficient way than cloning it to process a reference to it.
///   
///   **Example**:
///   ```rust
///   # use std::io::Read;
///   # use bytes::{NoInput, TryFromBytesDynamic};
///   // Some non-clonable type
///   struct Helper;
///   impl TryFromBytesDynamic<NoInput> for Helper {
///       type Error = std::convert::Infallible;
///       
///       #[inline]
///       fn try_from_bytes_dynamic(_input: NoInput, _reader: impl Read) -> Result<Self, Self::Error> {
///           Ok(Self)
///       }
///   }
///   
///   #[derive(TryFromBytesDynamic)]
///   #[bytes(dynamic_ty = "Helper", generate_refs = false)]
///   struct Example {
///       // Without `generate_refs`, this would've errored
///       #[bytes]
///       helper : Helper,
///   }
///   // Instead, implement our own for good practise
///   impl TryFromBytesDynamic<&Helper> for Example {
///       type Error = bytes::from_bytes::Error;
///       
///       #[inline]
///       fn try_from_bytes_dynamic(_input: &Helper, reader: impl Read) -> Result<Self, Self::Error> {
///           // We can rely on the generated one using another method of getting the input there
///           Self::try_from_bytes_dynamic(Helper, reader)
///       }
///   }
///   ```
/// 
/// ### Field-level attributes
/// - `#[bytes(enabled = <true|false>)`: Determines whether to parse/serialize this field.
///   This can be used in case `#[bytes(...)` needs to be given, but you don't want to enable
///   the parser/serializer; for example, you want to enable _only_ the parser/serializer but
///   not the other one (see the global `from`- and `to`-fields).
///   
///   **Example:**
///   ```rust
///   # use bytes::TryFromBytesDynamic;
///   #[derive(TryFromBytesDynamic)]
///   struct Example {
///       // We still don't parse this field!
///       #[bytes(enabled = false)]
///       not_parsed : std::path::PathBuf,
///   }
///   ```
/// - `#[bytes(name = "<NAME>")]`: Changes the name of this field for use in `input`-
///   expressions. Note that this doesn't change the field name.
///   
///   **Example:**
///   ```rust
///   # use bytes::TryFromBytesDynamic;
///   #[derive(TryFromBytesDynamic)]
///   struct Example {
///       // The field's name is `foo`...
///       #[bytes(name = "len")]
///       foo : usize,
///       // ...but we can refer to it as `len`!
///       #[bytes(input = len)]
///       bar : String,
///   }
///   ```
/// - `#[bytes(as_ty = "<TYPE>")]`: Attempts to parse a field using another type's parser/
///   serializer. For the parser, the result is converted into the target type using the `as`-type's
///   `Into<Field>` implementation. For serialization, the field type is first converted into
///   the target type using that type's `Into<Field>`-implementation and then serialized using
///   its implementation.
///   
///   Note: this attribute conflicts with `try_as_ty`.
///   
///   **Example:**
///   ```rust
///   # use bytes::TryFromBytesDynamic;
///   struct SomeType(u32);
///   impl From<u32> for SomeType {
///        fn from(value: u32) -> Self { Self(value) }
///   }
///   
///   #[derive(TryFromBytesDynamic)]
///   struct Example {
///       // For if 
///       #[bytes(as_ty = "u32")]
///       length : SomeType,
///   }
///   ```
/// - `#[bytes(try_as_ty = "<TYPE>")]`: Attempts to parse a field using another type's parser/
///   serializer. For the parser, the result is converted into the target type using the `as`-type's
///   `TryInto<Field>` implementation. For serialization, the field type is first converted into
///   the target type using that type's `TryInto<Field>`-implementation and then serialized using
///   its implementation.
///   
///   Note: this attribute conflicts with `as_ty`.
///   
///   **Example:**
///   ```rust
///   use std::convert::TryFrom;
///   # use bytes::TryFromBytesDynamic;
///   struct SomeType(u32);
///   impl TryFrom<u32> for SomeType {
///        type Error = std::convert::Infallible;
///        fn try_from(value: u32) -> Result<Self, Self::Error> { Ok(Self(value)) }
///   }
///   
///   #[derive(TryFromBytesDynamic)]
///   struct Example {
///       // For if 
///       #[bytes(try_as_ty = "u32")]
///       length : SomeType,
///   }
///   ```
/// - `#[bytes(input = <EXPR>)]`: Defines that the field uses
///   [`TryFromBytesDynamic`](trait@crate::TryFromBytesDynamic) instead of
///   [`TryFromBytes`](trait@crate::TryFromBytes) to provide the internal parser, and then
///   states the expression passed as the dynamic input. Note that this expression can include
///   the dynamic input value of the main struct as well as any _previous_ fields in the struct
///   declaration.
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
///       #[bytes(input = len + 5)]
///       txt : String,
///   }
///   ```
#[cfg(feature = "derive")]
pub mod procedural {
    /// Defines a procedural macro for deriving [`TryFromBytes`](trait@crate::TryFromBytes)
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
    ///     #[bytes(input = BigEndian)]
    ///     src_port : u16,
    ///     /// The packet destination port.
    ///     #[bytes(input = BigEndian)]
    ///     dst_port : u16,
    ///     /// The length of the packet, in bytes.
    ///     #[bytes(input = BigEndian)]
    ///     length   : u16,
    ///     /// A checksum for the datagram.
    ///     #[bytes(input = BigEndian)]
    ///     checksum : u16,
    /// }
    /// ```
    /// 
    /// Note that this trait is a shorthand for a
    /// [`TryFromBytesDynamic<NoInput>`](trait@crate::TryFromBytesDynamic<NoInput>), which implies a dynamic
    /// struct without input. As such, the derivation procedure for the two is exactly the same,
    /// except that the toplevel has no `#[bytes(dynamic_name = ...)]` and `#[bytes(dynamic_ty = ...)]`
    /// fields (but the individual fields still do).
    /// 
    /// As such, we recommend you read the
    /// [`TryFromBytesDynamic`](crate::procedural)-macro documentation instead.
    #[allow(non_snake_case)]
    pub mod TryFromBytes {}
}
#[cfg(feature = "derive")]
pub use bytes_derive::{TryFromBytes, TryFromBytesDynamic, TryToBytes, TryToBytesDynamic};
