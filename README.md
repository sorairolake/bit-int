<!--
SPDX-FileCopyrightText: 2024 Shun Sakai

SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# bit-int

[![CI][ci-badge]][ci-url]
[![Version][version-badge]][version-url]
![MSRV][msrv-badge]
[![Docs][docs-badge]][docs-url]
![License][license-badge]

**bit-int** is a library for providing arbitrary fixed bit-width integers for
[Rust].

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bit-int = "0.1.1"
```

### Documentation

See the [documentation][docs-url] for more details.

## Minimum supported Rust version

The minimum supported Rust version (MSRV) of this library is v1.67.0.

## Source code

The upstream repository is available at
<https://github.com/sorairolake/bit-int.git>.

The source code is also available at:

- <https://gitlab.com/sorairolake/bit-int.git>
- <https://codeberg.org/sorairolake/bit-int.git>

## Changelog

Please see [CHANGELOG.adoc].

## Contributing

Please see [CONTRIBUTING.adoc].

## License

Copyright &copy; 2024 Shun Sakai (see [AUTHORS.adoc])

This library is distributed under the terms of either the _Apache License 2.0_
or the _MIT License_.

This project is compliant with version 3.2 of the [_REUSE Specification_]. See
copyright notices of individual files for more details on copyright and
licensing information.

[ci-badge]: https://img.shields.io/github/actions/workflow/status/sorairolake/bit-int/CI.yaml?branch=develop&style=for-the-badge&logo=github&label=CI
[ci-url]: https://github.com/sorairolake/bit-int/actions?query=branch%3Adevelop+workflow%3ACI++
[version-badge]: https://img.shields.io/crates/v/bit-int?style=for-the-badge&logo=rust
[version-url]: https://crates.io/crates/bit-int
[msrv-badge]: https://img.shields.io/crates/msrv/bit-int?style=for-the-badge&logo=rust
[docs-badge]: https://img.shields.io/docsrs/bit-int?style=for-the-badge&logo=docsdotrs&label=Docs.rs
[docs-url]: https://docs.rs/bit-int
[license-badge]: https://img.shields.io/crates/l/bit-int?style=for-the-badge
[Rust]: https://www.rust-lang.org/
[CHANGELOG.adoc]: CHANGELOG.adoc
[CONTRIBUTING.adoc]: CONTRIBUTING.adoc
[AUTHORS.adoc]: AUTHORS.adoc
[_REUSE Specification_]: https://reuse.software/spec/
