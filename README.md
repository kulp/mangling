# mangling

This library provides for reversibly generating identifiers (hereinafter "mangled names") that are valid under C-language rules, from arbitrary byte streams, while maintaining a measure of human readability.

Its functionality was hoisted out of a compiler that needed to translate identifiers for Java symbols (e.g. method names and signatures) into symbols valid for the generated assembly language. Although the mangling process can encode any stream of bytes into a (longer) string of ASCII characters, and then convert the output back again, it is not intended to provide general encoding/decoding facilities. Instead, it is meant to provide an easy, reliable way for compiler writers to generate human-recognizable identifiers without having to invent their own mangling scheme.

At present, only one mangling scheme is supported, with a fixed format defined in the library documentation. The mangling scheme is simple, and may not be original, but is not known to be shared with any other system, so no interoperability guarantees are provided. Future revisions may change the API to allow some level of configurability or replacement of the encoding scheme.

The library is still considered experimental, but the implementation is designed to have the following properties:

1. Totality (every byte stream can be encoded into a unique mangled name)
1. Injectivity (each mangled name can be decoded to a unique byte stream)

Additionally, the implementation seeks to meet the following desiderata, in order of priority:

1. Correctness (the implementation matches its documented behavior)
1. Consistency (the implementation behaves in a predictable manner)
1. Readability (mangled names are visibly related to input streams)
1. Compactness (mangled names are comparable in length to inputs)
1. Performance (processing is computationally efficient in time and space)

Any demonstrated failure to meet the requirements should be reported, and pull requests addressing such issues are welcomed.

Darren Kulp
darren@kulp.ch
2020-Apr-10
