# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2020-04-17
### Added
- Introduced a C-compatible interface (`mangling_mangle` and `mangling_demangle`).
### Changed
- Generalized the `mangle` interface to accept `Borrow<u8>` instead of just `u8`.

## [0.1.1] - 2020-04-10
### Changed
- Improved formatting of README.md to be more navigable.
- Updated dev-dependency on [quickcheck] to 0.9.

## [0.1.0] - 2020-04-10
### Added
- Initial public release on [crates.io], based on history extracted from [tyrga].

[crates.io]: https://crates.io
[quickcheck]: https://github.com/BurntSushi/quickcheck
[tyrga]: https://github.com/kulp/tyrga

