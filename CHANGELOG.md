# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

### Added

- Add `nanos()` methods and `NanosDuration` aliases alongside other units.
- Implement AddAssign and SubAssign for Instant and Duration, and
  MulAssign and DivAssign for Duration.

### Fixed

### Changed

## [v0.3.3]

### Changed

- Underlying const gcd implementation switched to the `gcd` crate.
- `Duration::convert` now `const`.

## [v0.3.2]

### Fixed

- `Duration::convert` did not do the right thing when getting close to maximum supported values.

## [v0.3.1]

### Added

- Added `CHANGELOG.md`

### Fixed

- Now supports a `defmt` version span (0.2 and 0.3 is supported)

[Unreleased]: https://github.com/korken89/fugit/compare/v0.3.3...HEAD
[v0.3.3]: https://github.com/korken89/fugit/compare/v0.3.2...v0.3.3
[v0.3.2]: https://github.com/korken89/fugit/compare/v0.3.1...v0.3.2
[v0.3.1]: https://github.com/korken89/fugit/compare/v0.3.0...v0.3.1
