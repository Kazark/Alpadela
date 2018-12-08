# SBinExpr

Binary S-Expressions for fast serialization of simple (i.e. non-recursive,
though lists are supported as a primitive) algebraic data types. The emphasis
here is simplicity, (de)serialization speed, and memory-efficiency, in that
order. This is intended to be a backend for a simple IDL (Interface Description
Language) that would allow simple, fast, typed, protocol-agnostic,
language-agnostic communication between processes.
