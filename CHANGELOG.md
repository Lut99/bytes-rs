# Changelog
This file keeps track of notable changes in between versions.

This project uses [semantic versioning](https://semver.org). As such, we will mark which are breaking changes.


## [1.1.0] - TODO
### Added
- Types implementing `Flags` now also implement `ParsedLength` properly.
- Proper docstring to `lib.rs` in `bytes` (i.e., the crate itself).

### Removed
- `impl<T: ParsedLength> ParsedLength for &T` and `impl<T: ParsedLength> ParsedLength for &mut T`

### Fixed
- Version number being incorrect in `Cargo.toml`



## [1.0.0] - 2023-09-22
Initial release!

### Added
- `TryFromBytes` trait & derive macro.
- `TryFromBytesDynamic` trait & derive macro.
    - With implementations for primitives, tightly-packed containers (tuples, arrays, vectors) and strings (`Cow<str>` and `String`).
- `ParsedLength` helper trait.
