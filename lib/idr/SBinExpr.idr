||| Serialization of simple (non-recursive, but with list as a primitive)
||| algebraic data types to what I call "binary S-Expressions". They are like
||| S-Expressions, but use binary characters instead of parentheses and spaces.
||| Atoms are machine words, minus binary \x00 - \x03, which we reserve; strings
||| (or really, binary blobs) are also supported. Type information is not
||| carried in the serialization; it is assumed that all parties have previously
||| agreed on the type and are in sync concerning the (de)serialization
||| mechanism.
|||
||| In the binary form we substitute \x00 <NUL> for space, \x01 <SOH> for
||| double-quote, \x02 <STX> for left parenthesis, \x03 <ETX> for right
||| parenthesis. Rather than quoting, <SOH> results in an error if it occurs in
||| blobs, for simplicity and speed. Quoting requires unquoting; dropping is a
||| performance hit only on one side. Though the format itself is encoded in
||| binary, we are not focused on transmitting binary data. We could of course
||| quote \x01 by doubling it or some such, but we are more interested in speed
||| than flexibility in this case. If we do need to send binary data, you can do
||| the escaping at an application level.
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
  -- Like Pair, but does allow dropping the parens. When printing, if the
  -- top-level is `Bare`, this is technically malformed, and should be formatted
  -- as if it were `Pair`. A parser should never spit out a top-level `Bare`.
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
  | TopLvlExprMalformed
  | UnexpectedControlChar ControlChar
  | UnterminatedBlob
  | UnterminatedList
  | MissingDeliminator
  | TrailingBytes (l : List Char ** NonEmpty l)
  | MissingSecond
  | MalformedPair

data BrokenSnd : List a -> Type where
  EmptySnd : BrokenSnd []
  -- Perhaps a bit of a misnomer, for l itself can be empty
  NonESnd : (l : List a) -> Smaller l (x :: xs) -> BrokenSnd (x :: xs)

consBrokenSnd : (x : a) -> BrokenSnd xs -> BrokenSnd (x :: xs)
consBrokenSnd _ EmptySnd = NonESnd [] (LTESucc LTEZero)
consBrokenSnd _ (NonESnd l z) = NonESnd l (lteSuccRight z)

tailSmaller : (x : a) -> (xs : List a) -> Smaller xs (x :: xs)
tailSmaller x [] = LTESucc LTEZero
tailSmaller x (y :: xs) = LTESucc $ tailSmaller y xs

break' : (a -> Bool) -> (l : List a) -> (List a, BrokenSnd l)
break' _ []      = ([], EmptySnd)
break' p (x::xs) =
  if p x
  then ([], NonESnd xs $ tailSmaller x xs)
  else let (ys, zs) = break' p xs in (x::ys, consBrokenSnd x zs)

||| The result of a parse
PResult : List Char -> Type -> Type
PResult x a = Either SBEParseError (a, (y : List Char ** Smaller y x))

||| A quotataion marker has already been encountered (and is not included in the
||| input string). Parse until a matching quotation marker is encountered.
parseBlob : (x : List Char) -> PResult x SBinExpr
parseBlob x =
  let (one, two) = break' (== (controlChar Quote)) x in
  case two of
    EmptySnd => Left UnterminatedBlob
    (NonESnd xs prf) => Right (Blob $ pack one, (xs ** prf))

||| Parse out a terminator
parseTerm : (x : List Char) -> PResult x ()
parseTerm [] = Left MalformedPair
parseTerm (x :: xs) =
  case parseCC x of
    Just Term => Right ((), (xs ** lteRefl))
    _ => Left UnterminatedList

||| Because of their beautiful relationship to recursion and thus to Idris'
||| totality checker, we parse from Haskell strings; even though Idris' base
||| string type is primitive. However, since when we print we are recursing on
||| the AST, we go straight to primitive Idris strings.
partial
parse : String -> Either SBEParseError SBinExpr
parse = parseTopLvl . unpack where
  mutual
    ||| Parse a top-level expresion
    partial
    parseTopLvl : List Char -> Either SBEParseError SBinExpr
    parseTopLvl [] = Left EmptySExprIllegal
    parseTopLvl (x :: xs) =
      case parseCC x of
        Nothing => if xs == [] then Right $ Atom x else Left TopLvlExprMalformed
        Just Quote => do
          blob <- parseBlob xs
          case blob of
            (expr, ([] ** _)) => pure expr
            _ => Left UnterminatedBlob
        Just Init => do
          (expr, (rem ** _)) <- parseList xs
          case rem of
            [] => Right expr
            (x' :: xs') => Left $ TrailingBytes (x' :: xs' ** IsNonEmpty)
        Just cc => Left $ UnexpectedControlChar cc

    ||| A pair/list inititializer/"open parenthesis" has already been
    ||| encountered (and is not included in the input string). Parse until
    ||| a matching pair/list terminator/"close parentheiss" is encountered.
    partial
    parseList : (x : List Char) -> PResult x SBinExpr
    parseList [] = Left UnterminatedList
    parseList (x :: xs) = do
      (exprs, (rem ** prf)) <- parseInnerList (x :: xs)
      ((), (rem' ** prf')) <- parseTerm rem
      case exprs of
        (expr1 :: expr2 :: exprs') =>
          let prf'' = lteTransitive prf' (lteSuccLeft prf)
          in Right (foldl Bare expr2 exprs', (rem' ** prf''))
        _ => Left MalformedPair

    ||| Parse out a "list", but without caring about parenthesis, only minding
    ||| deliminators.
    partial
    parseInnerList : (x : List Char) -> {auto prf : NonEmpty x}
                   -> PResult x (List SBinExpr)
    parseInnerList (x :: xs) = do
      (expr, (rem ** prf)) <- parseOne (x :: xs)
      case rem of
        -- Because we are not here parsing a top-level expression (an inner list
        -- will always be parentheized on the outside) to run out of characters
        -- here is to fail to terminate a list.
        [] => Left UnterminatedList
        (x' :: xs') =>
          case parseCC x' of
            Nothing => Left MissingSecond
            Just Term => pure ([expr], ((x' :: xs') ** prf))
            Just Delim =>
              case xs' of
                [] => Left MissingSecond
                (x'' :: xs'') => do
                  (exprs, (rem' ** prf')) <- parseInnerList (x'' :: xs'')
                  let prf'' = lteSuccRight $ lteSuccRight prf'
                  pure (expr :: exprs, (rem' ** lteTransitive prf'' prf))
            Just cc => Left $ UnexpectedControlChar cc

    partial
    parseOne : (x : List Char) -> {auto prf : NonEmpty x} -> PResult x SBinExpr
    parseOne (x :: xs) =
      case parseCC x of
        Nothing => Right (Atom x, (xs ** lteRefl))
        Just Quote => do
          (expr, (rem ** prf)) <- parseBlob xs
          pure (expr, (rem ** lteSuccRight prf))
        Just Init => do
          (expr, (rem ** prf)) <- parseList xs
          pure (expr, (rem ** lteSuccRight prf))
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
