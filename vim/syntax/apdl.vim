if exists("b:current_syntax")
    finish
endif

syntax match apdlKeyword /\<abstract\>/
syntax match apdlKeyword /\<atom\>/
syntax match apdlKeyword /\<string\>/
syntax match apdlKeyword /\<list\>/
syntax match apdlKeyword /\<data\>/
syntax match apdlKeyword /\<newtype\>/
syntax match apdlKeyword /\<request\>/
syntax match apdlKeyword /\<response\>/

highlight link apdlKeyword Keyword

syntax match apdlSymbol /=/
syntax match apdlSymbol /|/

highlight link apdlSymbol Operator

syntax match apdlDataOrType /[A-Z][a-z0-9]*/

highlight link apdlDataOrType String

" Primitive types
syntax match apdlPrimitive /\<List\>/
syntax match apdlPrimitive /\<String\>/
syntax match apdlPrimitive /\<Char\>/
syntax match apdlPrimitive /\<Int\>/
syntax match apdlPrimitive /\<Maybe\>/
syntax match apdlPrimitive /\<Either\>/
syntax match apdlPrimitive /\<Bool\>/
syntax match apdlPrimitive /\<Unit\>/
syntax match apdlPrimitive /\<Pair\>/

highlight link apdlPrimitive Identifier

syntax match apdlComment /--.*$/
" TODO: the following rule is overly simplistic
syntax match apdlComment /{-.*-}/

highlight link apdlComment Comment

let b:current_syntax = "apdl"

