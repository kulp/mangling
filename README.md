# mangling

[![crates.io](https://img.shields.io/crates/v/mangling.svg)](https://crates.io/crates/mangling)
[![Rust](https://github.com/kulp/mangling/workflows/Rust/badge.svg)](https://github.com/kulp/mangling/actions?query=workflow%3ARust+branch%3Adevelop)
[![codecov](https://codecov.io/gh/kulp/mangling/branch/develop/graph/badge.svg)](https://codecov.io/gh/kulp/mangling)
[![Docs.rs](https://docs.rs/mangling/badge.svg)](https://docs.rs/mangling/)
![rustc 1.42+](https://img.shields.io/badge/rustc-1.42+-yellow.svg)

## Purpose
This library provides for reversibly generating identifiers (hereinafter "mangled names") that are valid under C-language rules, from arbitrary byte streams, while maintaining a measure of human readability.

## Rationale
The functionality of `mangling` was hoisted out of a compiler that needed to translate identifiers for Java symbols (e.g. method names and signatures) into symbols valid for the generated assembly language. Although the mangling process can encode any stream of bytes into a (longer) string of ASCII characters, and then convert the output back again, it is not intended to provide general encoding/decoding facilities. Instead, it is meant to provide an easy, reliable way for compiler writers to generate human-recognizable identifiers without having to invent their own mangling scheme.

## Features
### Schemes
At present, only one mangling scheme is supported, with a fixed format defined in the library documentation. The mangling scheme is simple, and may not be original, but is not known to be shared with any other system, so no interoperability guarantees are provided. Future revisions may change the API to allow some level of configurability or replacement of the encoding scheme.

### Requirements
1. Totality (every byte stream can be encoded into a unique mangled name)
1. Injectivity (each mangled name can be decoded to a unique byte stream)

### Goals
1. Correctness (the implementation matches its documented behavior)
1. Consistency (the implementation behaves in a predictable manner)
1. Readability (mangled names are visibly related to input streams)
1. Compactness (mangled names are comparable in length to inputs)
1. Performance (processing is computationally efficient in time and space)

## Feedback
Any demonstrated failure of `mangling` to meet its stated requirements should be reported through Github, and pull requests are welcomed.

