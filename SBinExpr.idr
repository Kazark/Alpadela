||| Serialization of simple (non-recursive, but with list as a primitive)
||| algebraic data types to what I call "binary S-Expressions". They are like
||| S-Expressions, but use binary characters instead of parentheses and spaces.
||| Atoms are machine words, minus binary \x00 - \x03, which we reserve; strings
||| are also supported (or really, binary blobs). Type information is not
||| carried in the serialization; it is assumed that all parties have previously
||| agreed on the type and are in sync concerning the (de)serialization
||| mechanism.
|||
||| In the binary form we substitute \x00 <NUL> for space, \x01 <SOH> for
||| double-quote, \x02 <STX> for left parenthesis, \x03 <ETX> for right
||| parenthesis. Rather than quoting, <SOH> is results in an error for blobs for
||| simplicity and speed. Quoting requires unquoting; dropping is a performance
||| hit only on one side. Though the format itself is encoded in binary, really
||| we are not focused on transmitting binary data. We could of course quote
||| \x01 by doubling it or some such, but we are more interested in speed than
||| flexibility in this case. If we do need to send binary data, we could
||| probably trade off a bit of performance in that specific case with a bit of
||| bit-remapping as a means of escaping, unless your binary data really cannot
||| be limited by even a single bit. In that case perhaps the protocol should
||| have an option to quote.
|||
||| We inject the word "binary" into the middle of the sentence rather than the
||| beginning for propriety's sake if you are one of those people who likes to
||| pronounce abbreviations. ;)
|||
||| This is intended as a reference implementation.
module SBinExpr

%default total
%access export

||| Abstract syntax tree for binary S-expressions
data SBinExpr
  = Atom Char
  | Blob String
  | Pair SBinExpr SBinExpr
  -- Like Pair, but does allows dropping the parens
  | Bare SBinExpr SBinExpr

data ControlChar = Delim | Init | Term | Quote

controlChar : ControlChar -> Char
-- Deliminator for lists/tuples in binary S-expressions
controlChar Delim = '\NUL'
-- Initialization / start marker for lists/tuples in binary S-expressions
controlChar Init = '\STX'
-- Terminator / end marker for lists/tuples in binary S-expressions
controlChar Term = '\ETX'
-- Quote mark for strings/blobs in binary S-expressions
controlChar Quote = '\SOH'

controlCharMap : List (Char, ControlChar)
controlCharMap = map (\c => (controlChar c, c)) [Delim, Init, Term, Quote]

parseCC : Char -> Maybe ControlChar
parseCC c = lookup c controlCharMap

Show ControlChar where
  show = singleton . controlChar

delim : String
delim = show Delim

init : String
init = show Init

term : String
term = show Term

quote : String
quote = show Quote

data SBEParseError
  = EmptySExprIllegal
  | TopLvlExprLackingParens
  | UnexpectedControlChar ControlChar

parse : String -> Either SBEParseError SBinExpr
parse = parseTopLvl . unpack where
  parseTopLvl : List Char -> Either SBEParseError SBinExpr
  parseTopLvl [] = Left EmptySExprIllegal
  parseTopLvl (x :: xs) =
    case parseCC x of
      Nothing =>
        case xs of
          [] => Right $ Atom x
          _ :: _ => Left TopLvlExprLackingParens
      Just Quote => ?read_to_end_quote
      Just Init => ?read_list
      Just cc => Left $ UnexpectedControlChar cc

data PrintEr
  = ControlCharInAtom ControlChar
  | QuoteInBlob

private printSBE' : SBinExpr -> Either PrintEr String
printSBE' (Atom x) =
  case parseCC x of
    Just c => Left $ ControlCharInAtom c
    Nothing => Right $ singleton x
printSBE' (Blob s) =
  if isInfixOf quote s
  then Left QuoteInBlob
  else Right $ quote ++ s ++ quote
printSBE' (Pair x y) = do
  x' <- printSBE' x
  y' <- printSBE' y
  pure $ init ++ x' ++ delim ++ y' ++ term
printSBE' (Bare x y) = do
  x' <- printSBE' x
  y' <- printSBE' y
  pure $ x' ++ delim ++ y'

printSBE : SBinExpr -> Either PrintEr String
-- Ensure parenthesis at the top level; if we were to permit lacking parenthesis
-- at the top, the parse would be much less simple. Saving two bytes is not
-- worth the complexity.
printSBE (Bare x y) = printSBE' (Pair x y)
printSBE x = printSBE' x

||| Invariants we would enforce if we could:
|||  1. Discriminated unions are serialized by:
|||   i. Assigning each case a unique integer in `[4, MaxInt)`.
|||   ii. If the case has data, packing the data of the particular case into a
|||       Lisp-style list, tagged with the case's specific data.
|||   iii. If the case does not have data, its representation is purely its
|||        unique integer.
|||  2. Records are treated as single-case discriminated unions, where the tag
|||     can therefore be dropped, so really, they are just treated as an ordered
|||     list of fields, for some deterministic ordering of fields.
|||  3. Strings are serialized directly to blobs
|||
||| When serializing a list, `maybeCompact` is tried first; if a data type can
||| be smashed into a char, it can be encoded more efficiently as a string
||| rather than a full-on list.
|||
||| Ultimately, rather than implementing these here, we will implement an IDL
||| and all of this code will be generated in what language desired, and we will
||| trust the IDL compiler to get it right. This is just a spike.
interface ToSBinExpr a where
  toSBE : a -> SBinExpr
  maybeCompact : Maybe (a -> Char)

interface FromSBinExpr a where
  fromSBE : SBinExpr -> Maybe a

||| This instance is extremely straightforward by desing, as it is assumed that
||| strings and types that will want to serialize as strings will predominant,
||| and therefore the ability to serialize directly will greatly help
||| performance.
ToSBinExpr String where
  toSBE = Blob
  -- String, in the abstract, cannot be smashed into a single char
  maybeCompact = Nothing

serialize : ToSBinExpr a => a -> Either PrintEr String
serialize = printSBE . toSBE

ToSBinExpr Char where
  toSBE = Atom
  maybeCompact = Just id

ToSBinExpr Int where
  toSBE = Atom . cast
  maybeCompact = Just cast

boolToChar : Bool -> Char
boolToChar False = '\04'
boolToChar True = '\05'

ToSBinExpr Bool where
  toSBE = Atom . boolToChar
  maybeCompact = Just boolToChar

listToList : (a -> SBinExpr) -> List a -> SBinExpr
listToList f [] = Atom '\04' -- Nil
listToList f (x :: xs) = Pair (f x) (listToList' f xs) where
  listToList' : (a -> SBinExpr) -> List a -> SBinExpr
  listToList' f [] = Atom '\04' -- Nil
  listToList' f (x :: xs) = Bare (f x) (listToList' f xs)

listToSBE : (inst : ToSBinExpr a) => List a -> SBinExpr
listToSBE @{inst} =
  case maybeCompact @{inst} of
    Nothing => listToList toSBE
    Just compact => Blob . pack . map compact

ToSBinExpr a => ToSBinExpr (List a) where
  toSBE = listToSBE
  -- Foldabes, in the abstract, cannot be smashed into a single char
  maybeCompact = Nothing

ToSBinExpr a => ToSBinExpr (Maybe a) where
  toSBE Nothing = Atom '\04'
  toSBE (Just x) = Pair (Atom '\05') (toSBE x)
  maybeCompact = Nothing

(ToSBinExpr a, ToSBinExpr b) => ToSBinExpr (Either a b) where
  toSBE (Left l) = Pair (Atom '\04') (toSBE l)
  toSBE (Right r) = Pair (Atom '\05') (toSBE r)
  maybeCompact = Nothing

-- The optimization here to potentially serialize to string is not worth the
-- complexity, because tuples are inherently smallish in length, nor to
-- serialize them as lists at all. Serialize directly to S-Expr pairs.
(ToSBinExpr a, ToSBinExpr b) => ToSBinExpr (Pair a b) where
  toSBE (f, s) = Pair (toSBE f) (toSBE s)
  maybeCompact = Nothing

-- TODO: need to be able to convert `SBinExpr` to a plain-text, human-readable
-- format for viewing/debugging.

-- Examples

Example0 : Either String Bool
Example0 = Left "foo"

Example1 : Either String Bool
Example1 = Left "bar"

Example2 : Either String Bool
Example2 = Right True

Example3 : Either String Bool
Example3 = Right False

Example4 : Maybe (Either Int Char)
Example4 = Nothing

Example5 : Maybe (Either Int Char)
Example5 = Just (Right '%')

Example6 : Maybe (Either Int Char)
Example6 = Just (Left 1337)

Example7 : List (Either String (Int, (Bool, Char)))
Example7 =
  [ Left "Random example"
  , Right (5, True, '?')
  , Right (0, False, ' ')
  ]
