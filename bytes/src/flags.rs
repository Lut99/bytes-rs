//  FLAGS.rs
//    by Lut99
// 
//  Created:
//    20 Sep 2023, 17:11:27
//  Last edited:
//    11 Oct 2023, 21:51:00
//  Auto updated?
//    Yes
// 
//  Description:
//!   Defines a special parsable type for parsing bytes as a series of
//!   flags.
// 

use std::io::{Read, Write};
use std::ops::{Deref, DerefMut};

use crate::from::TryFromBytesDynamic;
use crate::no_input::NoInput;
use crate::to::TryToBytesDynamic;


/***** LIBRARY MACROS *****/
/// A macro for generating ad-hoc [`Flags`]-like types.
/// 
/// # Arguments
/// This macro takes as input a list of field names to generate. These fields are in-order of the flags that we're parsing.
/// 
/// For example:
/// ```rust
/// use bytes::{flags, TryFromBytes as _};
/// 
/// /// A test struct
/// flags! {
///     flags TestFlags {
///         flag1,
///         // Optionally, you can add the type
///         flag2: bool,
///         flag3,
///     }
/// };
/// 
/// let flags: TestFlags = TestFlags::try_from_bytes(&[ 0b10100000 ][..]).unwrap();
/// assert_eq!(flags.flag1, true);
/// assert_eq!(flags.flag2, false);
/// assert_eq!(flags.flag3, true);
/// ```
/// 
/// # Parsing size
/// The resulting parsing & serializer will pack the bits as tightly as possible. As such, the number of bytes required to parse/store the generated struct is `(<NUM_FIELDS> + 8 - 1) / 8`.
/// 
/// To pack the bits less tightly, use unnamed fields as simply empty space, e.g.:
/// ```rust
/// use bytes::{flags, TryFromBytes as _};
/// 
/// flags! {
///     flags SparseFlags {
///         flag1,
///         _res,
///         flag2,
///     }
/// }
/// 
/// let flags: SparseFlags = SparseFlags::try_from_bytes(&[ 0b10100000 ][..]).unwrap();
/// assert_eq!(flags.flag1, true);
/// assert_eq!(flags.flag2, true);
/// ```
#[macro_export]
macro_rules! flags {
    // Base-case, where we do nothing
    {} => {};
    // Base-case, where we ignore commas nothing
    {, $($t:tt)*} => { flags! { $($t)* } };

    // Base-case, where there's only one structs
    {
        $(#[$outer:meta])*
        $outer_vis:vis flags $name:ident {
            $($(#[$field_attr:meta])* $inner_vis:vis $field_name:ident $(:bool)?),* $(,)?
        }
        $($t:tt)*
    } => {
        $(#[$outer])*
        $outer_vis struct $name {
            $($(#[$field_attr])* $inner_vis $field_name : bool),*
        }
        impl ::bytes::from::TryFromBytesDynamic<::bytes::no_input::NoInput> for $name {
            type Error = ::bytes::from::Error;

            fn try_from_bytes_dynamic(_input: ::bytes::no_input::NoInput, mut reader: impl ::std::io::Read) -> ::std::result::Result<Self, Self::Error> {
                // Compute how many bytes we need to read
                const N_FLAGS: ::std::primitive::usize = flags!(count_fields : $($field_name),*);
                const N_BYTES: ::std::primitive::usize = (N_FLAGS + 8 - 1) / 8;

                // Read those bytes
                let mut bytes: [::std::primitive::u8; N_BYTES] = [0; N_BYTES];
                if let Err(err) = reader.read_exact(&mut bytes) { return ::std::result::Result::Err(::bytes::from::Error::Read { err }); }

                // Serialize the bytes to a list of flags
                let mut flags: [::std::primitive::bool; N_FLAGS] = [false; N_FLAGS];
                for i in 0..N_BYTES {
                    for j in 0..8 {
                        if i * 8 + j >= N_FLAGS { break; }
                        flags[i * 8 + j] = ((bytes[i] >> (7 - j)) & 0x1) == 1;
                    }
                }

                // Unpack the list
                let [ $($field_name),* ] = flags;

                // Ok, build self
                ::std::result::Result::Ok(Self {
                    $($field_name),*
                })
            }
        }
        impl ::bytes::to::TryToBytesDynamic<::bytes::no_input::NoInput> for $name {
            type Error = ::bytes::to::Error;

            fn try_to_bytes_dynamic(&self, _input: ::bytes::no_input::NoInput, mut writer: impl ::std::io::Write) -> ::std::result::Result<(), Self::Error> {
                // Compute how many bytes we need to read
                const N_FLAGS: ::std::primitive::usize = flags!(count_fields : $($field_name),*);
                const N_BYTES: ::std::primitive::usize = (N_FLAGS + 8 - 1) / 8;

                // Put the bytes into an array of bits
                let flags: [::std::primitive::bool; N_FLAGS] = [ $(self.$field_name),* ];

                // Write that sequentially to a series of bytes
                for i in 0..N_BYTES {
                    let mut res: ::std::primitive::u8 = 0x00;
                    for j in 0..8 {
                        if i * 8 + j >= N_FLAGS { break; }
                        if flags[i * 8 + j] { res |= 0x1 << (7 - j) }
                    }
                    if let ::std::result::Result::Err(err) = writer.write_all(&[ res ]) {
                        return ::std::result::Result::Err(::bytes::to::Error::Write { err });
                    }
                }

                // Done!
                ::std::result::Result::Ok(())
            }
        }

        // Generate any remaining tokens
        flags!{ $($t)* }
    };

    // Dope case: simply go nuts and count the number of fields given
    (count_fields :) => { 0 };
    (count_fields : $field:ident) => { 1 };
    (count_fields : $field:ident,$($fields:ident),+) => { 1 + flags!(count_fields : $($fields),+) };
}





/***** LIBRARY *****/
/// Implements a series of unnamed flags.
/// 
/// # Example
/// ```rust
/// use bytes::{Flags, TryFromBytes as _, TryToBytes as _};
/// 
/// assert_eq!(Flags::<3>::try_from_bytes(&[ 0b10100110 ][..]).unwrap(), Flags([ true, false, true ]));
/// assert_eq!(Flags::<8>::try_from_bytes(&[ 0b10100110 ][..]).unwrap(), Flags([ true, false, true, false, false, true, true, false ]));
/// assert_eq!(Flags::<12>::try_from_bytes(&[ 0b10100110, 0b00010000 ][..]).unwrap(), Flags([ true, false, true, false, false, true, true, false, false, false, false, true ]));
/// assert!(matches!(Flags::<12>::try_from_bytes(&[ 0b10100110 ][..]), Err(bytes::from::Error::Read { .. })));
/// 
/// let mut output: [u8; 1] = [0; 1];
/// assert!(Flags([true, false, true]).try_to_bytes(&mut output[..]).is_ok());
/// assert_eq!(output, [ 0b10100000 ]);
/// 
/// let mut output: [u8; 1] = [0; 1];
/// assert!(Flags([true, false, true, false, false, true, true, false]).try_to_bytes(&mut output[..]).is_ok());
/// assert_eq!(output, [ 0b10100110 ]);
/// 
/// let mut output: [u8; 2] = [0; 2];
/// assert!(Flags([true, false, true, false, false, true, true, false, false, false, false, true ]).try_to_bytes(&mut output[..]).is_ok());
/// assert_eq!(output, [ 0b10100110, 0b00010000 ]);
/// 
/// let mut output: [u8; 1] = [0; 1];
/// assert!(matches!(Flags([true, false, true, false, false, true, true, false, false, false, false, true ]).try_to_bytes(&mut output[..]), Err(bytes::to::Error::Write { .. })));
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Flags<const N: usize>(pub [bool; N]);

impl<const N: usize> Deref for Flags<N> {
    type Target = [bool; N];

    #[inline]
    fn deref(&self) -> &Self::Target { &self.0 }
}
impl<const N: usize> DerefMut for Flags<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<const N: usize> TryFromBytesDynamic<NoInput> for Flags<N> {
    type Error = crate::from::Error;

    fn try_from_bytes_dynamic(_input: NoInput, mut reader: impl Read) -> Result<Self, Self::Error> {
        // Compute how many bytes we need to read
        let n_bytes: usize = (N + 8 - 1) / 8;

        // Read those bytes
        let mut bytes: Vec<u8> = vec![0; n_bytes];
        if let Err(err) = reader.read_exact(&mut bytes) { return Err(crate::from::Error::Read { err }); }

        // Serialize the bytes to a list of flags
        let mut flags: [bool; N] = [false; N];
        for i in 0..n_bytes {
            for j in 0..8 {
                if i * 8 + j >= N { break; }
                flags[i * 8 + j] = ((bytes[i] >> (7 - j)) & 0x1) == 1;
            }
        }

        // Done!
        Ok(Self(flags))
    }
}
impl<const N: usize> TryToBytesDynamic<NoInput> for Flags<N> {
    type Error = crate::to::Error;

    fn try_to_bytes_dynamic(&self, _input: NoInput, mut writer: impl Write) -> Result<(), Self::Error> {
        // Compute how many bytes we need to read
        let n_bytes: usize = (N + 8 - 1) / 8;

        // Write that sequentially to a series of bytes
        for i in 0..n_bytes {
            let mut res: u8 = 0x00;
            for j in 0..8 {
                if i * 8 + j >= N { break; }
                if self.0[i * 8 + j] { res |= 0x1 << (7 - j) }
            }
            if let Err(err) = writer.write_all(&[ res ]) {
                return Err(crate::to::Error::Write { err });
            }
        }

        // Done!
        Ok(())
    }
}
