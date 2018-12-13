# Alpadela

## The ALgebraic PAyload DEscription LAnguage

* Language-agnostic (up to having implemented a backend for that language)
* Protocol-agnostic (up to any protocol allowing transfer of arbitrary binary
  data)
* Supports two serialization formats:
  * Plain-text S-Expressions
  * Binary S-Expressions

### Algebraic

It supports algebraic data types (and has an overall functional perspective,
serializing to two forms of S-expressions).

### Payload Description Language

It is similar to an IDL (Interface Description Language), but does not describe
the entire interface, only the payload.
