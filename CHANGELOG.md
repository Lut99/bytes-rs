# Changelog
This file keeps track of notable changes in between versions.

This project uses [semantic versioning](https://semver.org). As such, we will mark which are breaking changes.


## [2.0.0] - TODO
### Added
- Proper docstring to `lib.rs` in `bytes` (i.e., the crate itself).
- Ability to serialize to a stream of bytes too via the `TryToBytes`- and `TryToBytesDynamic`-traits.

### Changed
- Some derive macro attributes, i.e., `dynamic` to `input` and such (see `procedural` documentation for the current list). \[**breaking**\]
- `TryFromBytes` and `TryFromBytesDynamic` now work using generalized input types with the `std::io::Read`-trait. \[**breaking**\]
- `Flags` as a trait has been removed, now there's a `Flags` tuple-like implementation and a `flags!()`-macro. \[**breaking**\]
- `NoInput` instead of `()` to mean that a type does not use any dynamic input. \[**breaking**\]
- Simplified library implementations using macros.

### Fixed
- Version number being incorrect in `Cargo.toml`



## [1.0.0] - 2023-09-22
Initial release!

### Added
- `TryFromBytes` trait & derive macro.
- `TryFromBytesDynamic` trait & derive macro.
    - With implementations for primitives, tightly-packed containers (tuples, arrays, vectors) and strings (`Cow<str>` and `String`).
- `ParsedLength` helper trait.
