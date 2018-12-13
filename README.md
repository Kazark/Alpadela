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

### "Prelude" or base types

The following types are primitive in that they map directly to the
serialization format and have special handling, in that their exact encoding
may vary per target language:

* `List`
* `String`
* `Char`
* `Int`

The following types are not primitive in terms of mapping directly to the
serialization format, but are recognized without needing to be defined.

* `Maybe` 
  * Maps to `option` in F# by default. Can be overridden in the hint file.
* `Either`
  * Has no default mapping for F#, and so will be generated unless otherwise
    specified in the hint file.
* `Bool`
  * Target language will determine whether this is primitive in that language,
    or an algebraic data type.
* `Unit`
* `Pair`

`Void` is not supported since this is a data language, not a programming/proof
language.

### Further information

See [the examples](example.apdl) and their comments for more information.

### Outstanding questions

* What about imports? Do we we need to be able to import other contract files?
* Do we need a sort of hint file for code generation, specific to the backend?
  How much of a mapping should we allow? Should we have language-specific
  options? Do we have to support mapping both the type names and the data
  constructors?
* How to we tell it "here is what the type looks like, FYI, but it already
  exists as X in all the target languages"? The base types above allow us to
  dodge this question for a bit, perhaps, but ultimately this will likely
  matter.
* Should we make `String` configurable as to what type it maps to in the
  destination language?
* How should we handle tuples?
* Should we support record types? If so, Idris-inspired syntax would be nice:
  
    record Point =
      x : Float
      y : Float

* A fundamental thing we need to grapple with is whether the serialization is
  32-bit or 64-bit.
* What about having Float / Double as a `Prelude` type?

