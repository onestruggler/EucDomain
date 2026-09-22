-- This module is an Agda port of the module CommandLine of the
-- programs of the Haskell package newsynth (programs/CommandLine.hs).
--
-- It provides some functions that are useful in the processing of
-- command line options, and that are shared between several
-- algorithms.
--
-- Differences from Haskell:
--
-- * Haskell's "reads" at the types Integer, Int, [Int] and Double is
--   implemented here by a small port of the relevant parts of GHC's
--   lexer (Text.Read.Lex) and of GHC.Read: optional white space and
--   parentheses, a unary minus (possibly separated by white space),
--   decimal numbers with optional fraction and exponent, hexadecimal
--   (0x..) and octal (0o..) integers, and, for Double, NaN and
--   Infinity; the rest of the string must be empty. Numbers of type
--   Int wrap around modulo 2⁶⁴ as in Haskell (to-int64). The Double
--   value is the correctly rounded value of the rational number, with
--   GHC's range check (numberToRangedRational).
--
-- * parse-int returns an ℤ (Haskell: any Integral type r, via
--   fromInteger); callers wrap it to the intended machine type.
--
-- * The module is not --safe, because it binds Haskell's hPutStr on
--   stderr (the standard library has no output to stderr).

{-# OPTIONS --without-K --guardedness #-}

module Programs.CommandLine where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Float.Base as Float using (Float)
import Data.Integer.DivMod as IntD
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String)
open import Data.Unit.Base using (⊤ ; tt)
open import IO.Base using (IO ; lift ; _>>_)
import IO.Primitive.Core as Prim
open import System.Exit using (exitFailure)

-- ----------------------------------------------------------------------
-- * Output to stderr

postulate
  primHPutStrStderr : String -> Prim.IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# COMPILE GHC primHPutStrStderr = Data.Text.IO.hPutStr System.IO.stderr #-}

-- Write a string to stderr.
hPutStrStderr : String -> IO {0ℓ} ⊤
hPutStrStderr s = lift (primHPutStrStderr s)

-- Write a string and a newline to stderr.
hPutStrLnStderr : String -> IO {0ℓ} ⊤
hPutStrLnStderr s = hPutStrStderr (s String.++ "\n")

-- ----------------------------------------------------------------------
-- * Formatting of lists and strings

-- A general list-to-string function. Example:
--
--   string-of-list "{" ", " "}" "{}" show [1,2,3] = "{1, 2, 3}"
string-of-list : {T : Set} -> String -> String -> String -> String -> (T -> String) -> List T -> String
string-of-list lpar comma rpar nil string-of-elt [] = nil
string-of-list lpar comma rpar nil string-of-elt (h ∷ t) =
  lpar String.++ string-of-elt h String.++ string-of-tail t String.++ rpar
  where
    string-of-tail : _ -> String
    string-of-tail [] = ""
    string-of-tail (h ∷ t) = comma String.++ string-of-elt h String.++ string-of-tail t

-- ----------------------------------------------------------------------
-- * Option processing

-- Exit with an error message after a command line error. This also
-- outputs information on where to find command line help.
optfail : {A : Set} -> String -> IO A
optfail msg = do
  hPutStrStderr msg
  hPutStrLnStderr "Try --help for more info."
  exitFailure

-- ----------------------------------------------------------------------
-- ** A port of the relevant parts of Haskell's "reads"

private
  Str : Set
  Str = List Char

  _==c_ : Char -> Char -> Bool
  a ==c b = Char.toℕ a Nat.≡ᵇ Char.toℕ b

  elemc : Char -> Str -> Bool
  elemc c [] = false
  elemc c (x ∷ xs) = (c ==c x) ∨ elemc c xs

  eqStr : Str -> Str -> Bool
  eqStr [] [] = true
  eqStr (a ∷ as) (b ∷ bs) = (a ==c b) ∧ eqStr as bs
  eqStr _ _ = false

  _>>=ᵐ_ : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
  nothing >>=ᵐ f = nothing
  just x >>=ᵐ f = f x

  _<|>_ : {A : Set} -> Maybe A -> Maybe A -> Maybe A
  just x <|> _ = just x
  nothing <|> y = y

  skipSpaces : Str -> Str
  skipSpaces = List.dropWhileᵇ Char.isSpace

  -- The value of a digit in the given base (nothing if it is not a
  -- digit of that base).
  digit-value : ℕ -> Char -> Maybe ℕ
  digit-value base c =
    if (48 Nat.≤ᵇ n) ∧ (n Nat.≤ᵇ 57) then check (n Nat.∸ 48)
    else if (97 Nat.≤ᵇ n) ∧ (n Nat.≤ᵇ 102) then check (n Nat.∸ 87)
    else if (65 Nat.≤ᵇ n) ∧ (n Nat.≤ᵇ 70) then check (n Nat.∸ 55)
    else nothing
    where
      n = Char.toℕ c
      check : ℕ -> Maybe ℕ
      check d = if d Nat.<ᵇ base then just d else nothing

  -- munch the digits of the given base.
  munch-digits : ℕ -> Str -> List ℕ × Str
  munch-digits base [] = [] , []
  munch-digits base (c ∷ cs) with digit-value base c
  ... | nothing = [] , c ∷ cs
  ... | just d with munch-digits base cs
  ...   | ds , rest = d ∷ ds , rest

  -- munch1: at least one digit.
  munch1-digits : ℕ -> Str -> Maybe (List ℕ × Str)
  munch1-digits base s with munch-digits base s
  ... | [] , _ = nothing
  ... | ds@(_ ∷ _) , rest = just (ds , rest)

  val : ℕ -> List ℕ -> ℕ
  val base = List.foldl (λ acc d -> acc Nat.* base Nat.+ d) 0

  -- Haskell's lexeme type, restricted to what is needed here.
  data Number : Set where
    MkNumber : ℕ -> List ℕ -> Number
    MkDecimal : List ℕ -> Maybe (List ℕ) -> Maybe ℤ -> Number

  data Lexeme : Set where
    LNumber : Number -> Lexeme
    LIdent : Str -> Lexeme
    LPunc : Char -> Lexeme
    -- the symbol "-"
    LMinus : Lexeme
    -- any other lexeme
    LOther : Lexeme

  isPuncChar : Char -> Bool
  isPuncChar c = elemc c (String.toList ",;()[]{}`")

  isSymbolChar : Char -> Bool
  isSymbolChar c = elemc c (String.toList "!#$%&*+./<=>?@\\^|-~:")

  isIdsChar : Char -> Bool
  isIdsChar c = Char.isAlpha c ∨ (c ==c '_')

  isIdfChar : Char -> Bool
  isIdfChar c = Char.isAlpha c ∨ Char.isDigit c ∨ elemc c (String.toList "_'")

  lexFrac : Str -> Maybe (List ℕ) × Str
  lexFrac ('.' ∷ cs) with munch1-digits 10 cs
  ... | just (ds , rest) = just ds , rest
  ... | nothing = nothing , '.' ∷ cs
  lexFrac s = nothing , s

  lexExp : Str -> Maybe ℤ × Str
  lexExp s@(e ∷ cs) with (e ==c 'e') ∨ (e ==c 'E')
  ... | false = nothing , s
  ... | true = signed cs
    where
      unsigned : Str -> Maybe ℤ × Str
      unsigned t with munch1-digits 10 t
      ... | just (ds , rest) = just (+ val 10 ds) , rest
      ... | nothing = nothing , s

      signed : Str -> Maybe ℤ × Str
      signed ('-' ∷ t) with munch1-digits 10 t
      ... | just (ds , rest) = just (Int.- (+ val 10 ds)) , rest
      ... | nothing = nothing , s
      signed ('+' ∷ t) with munch1-digits 10 t
      ... | just (ds , rest) = just (+ val 10 ds) , rest
      ... | nothing = nothing , s
      signed t = unsigned t
  lexExp [] = nothing , []

  lexDecNumber : Str -> Maybe (Lexeme × Str)
  lexDecNumber s with munch1-digits 10 s
  ... | nothing = nothing
  ... | just (ds , rest) with lexFrac rest
  ...   | frac , rest2 with lexExp rest2
  ...     | ex , rest3 = just (LNumber (MkDecimal ds frac ex) , rest3)

  lexHexOct : Str -> Maybe (Lexeme × Str)
  lexHexOct ('0' ∷ b ∷ cs) = base-of b >>=ᵐ λ base -> munch1-digits base cs >>=ᵐ λ where
      (ds , rest) -> just (LNumber (MkNumber base ds) , rest)
    where
      base-of : Char -> Maybe ℕ
      base-of 'x' = just 16
      base-of 'X' = just 16
      base-of 'o' = just 8
      base-of 'O' = just 8
      base-of _ = nothing
  lexHexOct _ = nothing

  munch : (Char -> Bool) -> Str -> Str × Str
  munch p [] = [] , []
  munch p (c ∷ cs) with p c
  ... | false = [] , c ∷ cs
  ... | true with munch p cs
  ...   | a , b = c ∷ a , b

  -- Haskell's lex (after skipping white space). Lexemes that are not
  -- needed for reading numbers are returned as LOther (they only lead
  -- to parse failures).
  lexToken : Str -> Maybe (Lexeme × Str)
  lexToken [] = nothing
  lexToken s@(c ∷ cs) =
    if isPuncChar c then just (LPunc c , cs)
    else if isSymbolChar c then symbol (munch isSymbolChar s)
    else if Char.isDigit c then (lexHexOct s <|> lexDecNumber s)
    else if isIdsChar c then ident (munch isIdfChar cs)
    else just (LOther , cs)
    where
      symbol : Str × Str -> Maybe (Lexeme × Str)
      symbol ('-' ∷ [] , rest) = just (LMinus , rest)
      symbol (_ , rest) = just (LOther , rest)
      ident : Str × Str -> Maybe (Lexeme × Str)
      ident (name , rest) = just (LIdent (c ∷ name) , rest)

  lexP : Str -> Maybe (Lexeme × Str)
  lexP s = lexToken (skipSpaces s)

  -- GHC.Read's readNumber: an optional minus sign followed by a
  -- number lexeme, converted by conv.
  readNumber : {A : Set} -> (Lexeme -> Maybe A) -> (A -> A) -> Str -> Maybe (A × Str)
  readNumber conv neg s = lexP s >>=ᵐ λ where
    (LMinus , r) -> lexP r >>=ᵐ λ where
      (y , r') -> conv y >>=ᵐ λ n -> just (neg n , r')
    (x , r) -> conv x >>=ᵐ λ n -> just (n , r)

  -- GHC.Read's parens: optional parentheses (the first argument is
  -- fuel; each level of parentheses consumes a character).
  close-paren : {A : Set} -> A × Str -> Maybe (A × Str)
  close-paren (x , r) with skipSpaces r
  ... | ')' ∷ r' = just (x , r')
  ... | _ = nothing

  parens' : {A : Set} -> ℕ -> (Str -> Maybe (A × Str)) -> Str -> Maybe (A × Str)
  parens' zero p s = p s
  parens' (suc f) p s = p s <|> mandatory (skipSpaces s)
    where
      mandatory : Str -> Maybe (_ × Str)
      mandatory ('(' ∷ r) = parens' f p r >>=ᵐ close-paren
      mandatory _ = nothing

  parens : {A : Set} -> (Str -> Maybe (A × Str)) -> Str -> Maybe (A × Str)
  parens p s = parens' (List.length s) p s

  -- numberToInteger.
  convertInt : Lexeme -> Maybe ℤ
  convertInt (LNumber (MkNumber base ds)) = just (+ val base ds)
  convertInt (LNumber (MkDecimal ds nothing nothing)) = just (+ val 10 ds)
  convertInt _ = nothing

  pow10 : ℕ -> ℕ
  pow10 n = 10 Nat.^ n

  -- numberToRational, as a fraction (numerator, denominator > 0).
  numberToRational : Number -> ℤ × ℕ
  numberToRational (MkNumber base ds) = + val base ds , 1
  numberToRational (MkDecimal ds frac ex) = scale ex (mant frac)
    where
      mant : Maybe (List ℕ) -> ℕ × ℕ
      mant nothing = val 10 ds , 1
      mant (just fs) = val 10 (ds ++ fs) , pow10 (List.length fs)
      scale : Maybe ℤ -> ℕ × ℕ -> ℤ × ℕ
      scale nothing (a , b) = + a , b
      scale (just (+ e)) (a , b) = + (a Nat.* pow10 e) , b
      scale (just -[1+ e ]) (a , b) = + a , b Nat.* pow10 (suc e)

  -- Haskell's maxBound :: Int.
  maxInt : ℕ
  maxInt = 9223372036854775807

  -- numberToRangedRational (-1021, 1024), for Double: nothing means
  -- infinity.
  numberToRangedRational : Number -> Maybe (ℤ × ℕ)
  numberToRangedRational n@(MkDecimal ds frac (just ex)) =
    if too-large ex then nothing
    else if too-small ex then just (+ 0 , 1)
    else first-digit (List.dropWhileᵇ (λ d -> d Nat.≡ᵇ 0) ds) frac
    where
      -- exponents outside the range of Int (as observed with GHC 9.10:
      -- 1e-99999999999999999999 reads as 0.0)
      too-large : ℤ -> Bool
      too-large (+ e) = maxInt Nat.<ᵇ e
      too-large -[1+ e ] = false
      too-small : ℤ -> Bool
      too-small (+ e) = false
      too-small -[1+ e ] = maxInt Nat.<ᵇ e

      check : ℤ -> Maybe (ℤ × ℕ)
      check fd' = if (+ 1027) Int.<ᵇ fd' then nothing
                  else if fd' Int.<ᵇ Int.- (+ 1024) then just (+ 0 , 1)
                  else just (numberToRational n)

      first-digit : List ℕ -> Maybe (List ℕ) -> Maybe (ℤ × ℕ)
      first-digit ds'@(_ ∷ _) _ = check (+ List.length ds' Int.+ ex)
      first-digit [] nothing = just (+ 0 , 1)
      first-digit [] (just fs) with List.dropWhileᵇ (λ d -> d Nat.≡ᵇ 0) fs
      ... | [] = just (+ 0 , 1)
      ... | _ ∷ _ = check (Int.- (+ List.length (List.takeWhileᵇ (λ d -> d Nat.≡ᵇ 0) fs)) Int.+ ex)
  numberToRangedRational n = just (numberToRational n)

  convertFrac : Lexeme -> Maybe Float
  convertFrac (LIdent s) =
    if eqStr s (String.toList "NaN") then just (0.0 Float.÷ 0.0)
    else if eqStr s (String.toList "Infinity") then just (1.0 Float.÷ 0.0)
    else nothing
  convertFrac (LNumber n) with numberToRangedRational n
  ... | nothing = just (1.0 Float.÷ 0.0)
  ... | just (a , b) = just (Float.fromRatio a (+ b))
  convertFrac _ = nothing

  -- Accept a complete parse only (Haskell: [(n, "")]).
  complete : {A : Set} -> Maybe (A × Str) -> Maybe A
  complete (just (x , [])) = just x
  complete _ = nothing

  readInteger : Str -> Maybe (ℤ × Str)
  readInteger = parens (readNumber convertInt (λ x -> Int.- x))

-- Wrap an integer to the range of Haskell's Int (64 bits), as
-- fromInteger does.
to-int64 : ℤ -> ℤ
to-int64 n = + ((n Int.+ + 9223372036854775808) IntD.%ℕ 18446744073709551616) Int.- + 9223372036854775808

-- Parse a string to an integer, or return nothing on failure (Haskell:
-- reads at type Integer).
parse-int : String -> Maybe ℤ
parse-int s = complete (readInteger (String.toList s))

-- Parse a string to a list of integers (of type Int), or return
-- nothing on failure.
parse-list-int : String -> Maybe (List ℤ)
parse-list-int s = complete (parens list (String.toList s))
  where
    readInt : Str -> Maybe (ℤ × Str)
    readInt t = readInt' t
      where
        readInt' : Str -> Maybe (ℤ × Str)
        readInt' u = readInteger u >>=ᵐ λ where (n , r) -> just (to-int64 n , r)

    -- listRest started, with fuel.
    listRest : ℕ -> Bool -> Str -> Maybe (List ℤ × Str)
    listNext : ℕ -> Str -> Maybe (List ℤ × Str)
    listRest zero _ _ = nothing
    listRest (suc f) started t = lexP t >>=ᵐ λ where
      (LPunc ']' , r) -> just ([] , r)
      (LPunc ',' , r) -> if started then listNext f r else nothing
      _ -> nothing
    listNext zero _ = nothing
    listNext (suc f) t = readInt t >>=ᵐ λ where
      (x , r) -> listRest f true r >>=ᵐ λ where
        (xs , r') -> just (x ∷ xs , r')

    list : Str -> Maybe (List ℤ × Str)
    list t = lexP t >>=ᵐ λ where
      (LPunc '[' , r) -> listRest (List.length r) false r <|> listNext (List.length r) r
      _ -> nothing

-- Parse a string to a Float (Haskell: Double), or return nothing on
-- failure.
parse-double : String -> Maybe Float
parse-double s = complete (parens (readNumber convertFrac (λ x -> Float.- x)) (String.toList s))

-- ----------------------------------------------------------------------
-- ** Enumerations

-- In an association list, find the key that best matches the given
-- string. If one key matches exactly, return the corresponding
-- key-value pair. Otherwise, return a list of all key-value pairs
-- whose key have the given string as a prefix. This list could be of
-- length 0 (no match), 1 (unique match), or greater (ambiguous key).
-- Note: the keys in the association list must be lower case. The
-- input string is converted to lower case as well, resulting in
-- case-insensitive matching.
match-enum : {A : Set} -> List (String × A) -> String -> List (String × A)
match-enum {A} list key = go (lookup list)
  where
    s : Str
    s = List.map Char.toLower (String.toList key)

    lookup : List (String × A) -> Maybe A
    lookup [] = nothing
    lookup ((k , v) ∷ rest) = if eqStr (String.toList k) s then just v else lookup rest

    isPrefixOf : Str -> Str -> Bool
    isPrefixOf [] _ = true
    isPrefixOf (a ∷ as) [] = false
    isPrefixOf (a ∷ as) (b ∷ bs) = (a ==c b) ∧ isPrefixOf as bs

    go : Maybe A -> List (String × A)
    go (just v) = (String.fromList s , v) ∷ []
    go nothing = List.filterᵇ (λ kv -> isPrefixOf s (String.toList (proj₁ kv))) list

-- Pretty-print a list of possible values for a parameter. The first
-- argument is the name of the parameter, and the second argument is
-- its enumeration.
show-enum : {A : Set} -> String -> List (String × A) -> String
show-enum param list =
  "Possible values for " String.++ param String.++ " are: " String.++
  string-of-list "" ", " "" "no possible values" proj₁ list String.++ ".\n"
