-- This module is an Agda port of the module Quantum.Synthesis.SymReal
-- of the Haskell package newsynth.
--
-- It provides a symbolic representation of real number expressions,
-- and a parser for such expressions (used for the angle argument of
-- the gridsynth command line tool).
--
-- The class ToReal and the functions dynamic-fixedprec and
-- dynamic-fixedprec2, which Haskell defines (a second time) in this
-- module, are those of Quantum.Synthesis.ToReal, re-exported from
-- here; this module adds the ToReal instances for SymReal and String.
--
-- Note: the constructor ArcTan2 clashes with the class ArcTan2 of
-- Quantum.Synthesis.ArcTan2; modules importing both should import one
-- of them with renaming or hiding.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.SymReal where

open import Data.Bool.Base using (Bool ; true ; false ; not ; if_then_else_ ; _∧_ ; _∨_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe ; just ; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Rational.Base as Rat using (ℚ)
open import Data.String.Base as String using (String ; _++_)
import Data.String.Properties as StrP
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; sym ; trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Data.Number.FixedPrec
open Data.Number.FixedPrec.Aux using (divide)
open import Quantum.Synthesis.ArcTan2 renaming (ArcTan2 to ArcTan2-class)
open import Quantum.Synthesis.ToReal public

-- ----------------------------------------------------------------------
-- * Symbolic real number expressions

-- A type to represent symbolic expressions for real numbers.
--
-- Caution: equality _≟_ at this type denotes symbolic equality of
-- expressions, not equality of the defined real numbers.
data SymReal : Set where
  -- An integer constant.
  Const : ℤ -> SymReal
  -- A decimal constant. This has a rational value and a string
  -- representation.
  Decimal : ℚ -> String -> SymReal
  -- x + y, x − y, x * y, x / y.
  Plus Minus Times Div : SymReal -> SymReal -> SymReal
  -- −x, |x|, signum(x), 1/x.
  Negate Abs Signum Recip : SymReal -> SymReal
  -- π, e.
  Pi Euler : SymReal
  -- exp x, √x, log x.
  Exp Sqrt Log : SymReal -> SymReal
  -- xʸ.
  Power : SymReal -> SymReal -> SymReal
  Sin Tan Cos ASin ATan ACos : SymReal -> SymReal
  Sinh Tanh Cosh ASinh ATanh ACosh : SymReal -> SymReal
  -- arctan2 y x.
  ArcTan2 : SymReal -> SymReal -> SymReal

-- ----------------------------------------------------------------------
-- ** Printing

showsPrec-SymReal : ℕ -> SymReal -> String
showsPrec-SymReal d (Const x) = showsPrec d x
showsPrec-SymReal d (Decimal x s) = s
showsPrec-SymReal d (Plus x y) = showParen d 6 (showsPrec-SymReal 6 x ++ "+" ++ showsPrec-SymReal 6 y)
showsPrec-SymReal d (Minus x y) = showParen d 6 (showsPrec-SymReal 6 x ++ "-" ++ showsPrec-SymReal 7 y)
showsPrec-SymReal d (Times x y) = showParen d 7 (showsPrec-SymReal 7 x ++ "*" ++ showsPrec-SymReal 7 y)
showsPrec-SymReal d (Div x y) = showParen d 7 (showsPrec-SymReal 7 x ++ "/" ++ showsPrec-SymReal 8 y)
showsPrec-SymReal d (Power x y) = showParen d 8 (showsPrec-SymReal 9 x ++ "**" ++ showsPrec-SymReal 9 y)
showsPrec-SymReal d (Negate x) = showParen d 5 ("-" ++ showsPrec-SymReal 7 x)
showsPrec-SymReal d (Abs x) = showParen d 10 ("abs " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Signum x) = showParen d 10 ("signum " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Recip x) = showParen d 7 ("1/" ++ showsPrec-SymReal 8 x)
showsPrec-SymReal d Pi = "pi"
showsPrec-SymReal d Euler = "e"
showsPrec-SymReal d (Exp x) = showParen d 10 ("exp " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Sqrt x) = showParen d 10 ("sqrt " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Log x) = showParen d 10 ("log " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Sin x) = showParen d 10 ("sin " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Tan x) = showParen d 10 ("tan " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Cos x) = showParen d 10 ("cos " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (ASin x) = showParen d 10 ("asin " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (ATan x) = showParen d 10 ("atan " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (ACos x) = showParen d 10 ("acos " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Sinh x) = showParen d 10 ("sinh " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Tanh x) = showParen d 10 ("tanh " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (Cosh x) = showParen d 10 ("cosh " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (ASinh x) = showParen d 10 ("asinh " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (ATanh x) = showParen d 10 ("atanh " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (ACosh x) = showParen d 10 ("acosh " ++ showsPrec-SymReal 11 x)
showsPrec-SymReal d (ArcTan2 y x) =
  showParen d 10 ("arctan2 " ++ showsPrec-SymReal 11 y ++ " " ++ showsPrec-SymReal 11 x)

-- ----------------------------------------------------------------------
-- ** Symbolic equality

-- Decidable (symbolic) equality is proved via an injective encoding
-- into a small tree type (Haskell: deriving Eq).
private
  data Tree : Set where
    tZ : ℤ -> Tree
    tQ : ℚ -> String -> Tree
    tL : Tree
    tN : ℕ -> Tree -> Tree -> Tree

  _≟T_ : DecidableEquality Tree
  tZ a ≟T tZ b with a ≟ b
  ... | yes refl = yes refl
  ... | no ne = no λ { refl -> ne refl }
  tQ a s ≟T tQ b t with a ≟ b | s StrP.≟ t
  ... | yes refl | yes refl = yes refl
  ... | no ne | _ = no λ { refl -> ne refl }
  ... | yes _ | no ne = no λ { refl -> ne refl }
  tL ≟T tL = yes refl
  tN k a b ≟T tN l c d with k ≟ l | a ≟T c | b ≟T d
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ne | _ | _ = no λ { refl -> ne refl }
  ... | yes _ | no ne | _ = no λ { refl -> ne refl }
  ... | yes _ | yes _ | no ne = no λ { refl -> ne refl }
  tZ _ ≟T tQ _ _ = no λ ()
  tZ _ ≟T tL = no λ ()
  tZ _ ≟T tN _ _ _ = no λ ()
  tQ _ _ ≟T tZ _ = no λ ()
  tQ _ _ ≟T tL = no λ ()
  tQ _ _ ≟T tN _ _ _ = no λ ()
  tL ≟T tZ _ = no λ ()
  tL ≟T tQ _ _ = no λ ()
  tL ≟T tN _ _ _ = no λ ()
  tN _ _ _ ≟T tZ _ = no λ ()
  tN _ _ _ ≟T tQ _ _ = no λ ()
  tN _ _ _ ≟T tL = no λ ()

  u : ℕ -> Tree -> Tree
  u k a = tN k a tL

  encode : SymReal -> Tree
  encode (Const x) = tZ x
  encode (Decimal x s) = tQ x s
  encode Pi = tN 0 tL tL
  encode Euler = tN 1 tL tL
  encode (Negate x) = u 2 (encode x)
  encode (Abs x) = u 3 (encode x)
  encode (Signum x) = u 4 (encode x)
  encode (Recip x) = u 5 (encode x)
  encode (Exp x) = u 6 (encode x)
  encode (Sqrt x) = u 7 (encode x)
  encode (Log x) = u 8 (encode x)
  encode (Sin x) = u 9 (encode x)
  encode (Tan x) = u 10 (encode x)
  encode (Cos x) = u 11 (encode x)
  encode (ASin x) = u 12 (encode x)
  encode (ATan x) = u 13 (encode x)
  encode (ACos x) = u 14 (encode x)
  encode (Sinh x) = u 15 (encode x)
  encode (Tanh x) = u 16 (encode x)
  encode (Cosh x) = u 17 (encode x)
  encode (ASinh x) = u 18 (encode x)
  encode (ATanh x) = u 19 (encode x)
  encode (ACosh x) = u 20 (encode x)
  encode (Plus x y) = tN 21 (encode x) (encode y)
  encode (Minus x y) = tN 22 (encode x) (encode y)
  encode (Times x y) = tN 23 (encode x) (encode y)
  encode (Div x y) = tN 24 (encode x) (encode y)
  encode (Power x y) = tN 25 (encode x) (encode y)
  encode (ArcTan2 x y) = tN 26 (encode x) (encode y)

  lift2 : (SymReal -> SymReal -> SymReal) -> Maybe SymReal -> Maybe SymReal -> Maybe SymReal
  lift2 f (just x) (just y) = just (f x y)
  lift2 f _ _ = nothing

  unary : ℕ -> SymReal -> SymReal
  unary k x =
    if k Nat.≡ᵇ 2 then Negate x
    else if k Nat.≡ᵇ 3 then Abs x
    else if k Nat.≡ᵇ 4 then Signum x
    else if k Nat.≡ᵇ 5 then Recip x
    else if k Nat.≡ᵇ 6 then Exp x
    else if k Nat.≡ᵇ 7 then Sqrt x
    else if k Nat.≡ᵇ 8 then Log x
    else if k Nat.≡ᵇ 9 then Sin x
    else if k Nat.≡ᵇ 10 then Tan x
    else if k Nat.≡ᵇ 11 then Cos x
    else if k Nat.≡ᵇ 12 then ASin x
    else if k Nat.≡ᵇ 13 then ATan x
    else if k Nat.≡ᵇ 14 then ACos x
    else if k Nat.≡ᵇ 15 then Sinh x
    else if k Nat.≡ᵇ 16 then Tanh x
    else if k Nat.≡ᵇ 17 then Cosh x
    else if k Nat.≡ᵇ 18 then ASinh x
    else if k Nat.≡ᵇ 19 then ATanh x
    else ACosh x

  binary : ℕ -> SymReal -> SymReal -> SymReal
  binary k x y =
    if k Nat.≡ᵇ 21 then Plus x y
    else if k Nat.≡ᵇ 22 then Minus x y
    else if k Nat.≡ᵇ 23 then Times x y
    else if k Nat.≡ᵇ 24 then Div x y
    else if k Nat.≡ᵇ 25 then Power x y
    else ArcTan2 x y

  decodeN : ℕ -> Maybe SymReal -> Maybe SymReal -> Maybe SymReal
  decodeN k ma mb =
    if k Nat.≡ᵇ 0 then just Pi
    else if k Nat.≡ᵇ 1 then just Euler
    else if k Nat.<ᵇ 21 then Maybe.map (unary k) ma
    else if k Nat.<ᵇ 27 then lift2 (binary k) ma mb
    else nothing

  decode : Tree -> Maybe SymReal
  decode (tZ x) = just (Const x)
  decode (tQ x s) = just (Decimal x s)
  decode tL = nothing
  decode (tN k a b) = decodeN k (decode a) (decode b)

  decode-encode : (x : SymReal) -> decode (encode x) ≡ just x
  decode-encode (Const x) = refl
  decode-encode (Decimal x s) = refl
  decode-encode Pi = refl
  decode-encode Euler = refl
  decode-encode (Negate x) rewrite decode-encode x = refl
  decode-encode (Abs x) rewrite decode-encode x = refl
  decode-encode (Signum x) rewrite decode-encode x = refl
  decode-encode (Recip x) rewrite decode-encode x = refl
  decode-encode (Exp x) rewrite decode-encode x = refl
  decode-encode (Sqrt x) rewrite decode-encode x = refl
  decode-encode (Log x) rewrite decode-encode x = refl
  decode-encode (Sin x) rewrite decode-encode x = refl
  decode-encode (Tan x) rewrite decode-encode x = refl
  decode-encode (Cos x) rewrite decode-encode x = refl
  decode-encode (ASin x) rewrite decode-encode x = refl
  decode-encode (ATan x) rewrite decode-encode x = refl
  decode-encode (ACos x) rewrite decode-encode x = refl
  decode-encode (Sinh x) rewrite decode-encode x = refl
  decode-encode (Tanh x) rewrite decode-encode x = refl
  decode-encode (Cosh x) rewrite decode-encode x = refl
  decode-encode (ASinh x) rewrite decode-encode x = refl
  decode-encode (ATanh x) rewrite decode-encode x = refl
  decode-encode (ACosh x) rewrite decode-encode x = refl
  decode-encode (Plus x y) rewrite decode-encode x | decode-encode y = refl
  decode-encode (Minus x y) rewrite decode-encode x | decode-encode y = refl
  decode-encode (Times x y) rewrite decode-encode x | decode-encode y = refl
  decode-encode (Div x y) rewrite decode-encode x | decode-encode y = refl
  decode-encode (Power x y) rewrite decode-encode x | decode-encode y = refl
  decode-encode (ArcTan2 x y) rewrite decode-encode x | decode-encode y = refl

  encode-injective : {x y : SymReal} -> encode x ≡ encode y -> x ≡ y
  encode-injective {x} {y} eq =
    just-injective (trans (sym (decode-encode x)) (trans (cong decode eq) (decode-encode y)))

-- ----------------------------------------------------------------------
-- ** Instances

instance
  ShowSymReal : Show SymReal
  ShowSymReal .showsPrec = showsPrec-SymReal

  DecEqSymReal : DecEq SymReal
  DecEqSymReal ._≟_ x y with encode x ≟T encode y
  ... | yes eq = yes (encode-injective eq)
  ... | no ne = no λ eq -> ne (cong encode eq)

  -- Note: Haskell's x - y is Minus x y, whereas the framework's
  -- derived x - y is x + (- y), i.e. Plus x (Negate y). Similarly
  -- fromℤ -3 is Negate (Const 3) rather than Const -3. Use the
  -- constructors directly when the exact symbolic form matters.
  SemiRingSymReal : SemiRing SymReal
  SemiRingSymReal ._+_ = Plus
  SemiRingSymReal ._*_ = Times
  SemiRingSymReal .0# = Const 0
  SemiRingSymReal .1# = Const 1
  SemiRingSymReal .fromℕ n = Const (+ n)

  RingSymReal : Ring SymReal
  RingSymReal .sra = SemiRingSymReal
  RingSymReal .-_ = Negate

  NumberSymReal : Number SymReal
  NumberSymReal = number-from-semiring

  NegativeSymReal : Negative SymReal
  NegativeSymReal = negative-from-ring

  -- Division is symbolic, so NonZero is trivial.
  NonZeroSymReal : NonZeroTypeclass SymReal
  NonZeroSymReal = nonZeroTypeclass-trivial

  DivModSymReal : DivMod SymReal
  DivModSymReal .NZT = NonZeroSymReal
  DivModSymReal ._/_ x y = Div x y
  DivModSymReal ._%_ x y = Const 0

  FractionalSymReal : Fractional SymReal
  FractionalSymReal .DM = DivModSymReal
  FractionalSymReal ._⁻¹ x = Recip x
  FractionalSymReal .fromℚ q = Div (Const (Rat.↥ q)) (Const (+ Rat.↧ₙ q))

  FloatingSymReal : Floating SymReal
  FloatingSymReal .π = Pi
  FloatingSymReal .exp = Exp
  FloatingSymReal .log = Log
  FloatingSymReal .sqrt = Sqrt
  FloatingSymReal .sin = Sin
  FloatingSymReal .cos = Cos
  FloatingSymReal .tan = Tan
  FloatingSymReal .asin = ASin
  FloatingSymReal .acos = ACos
  FloatingSymReal .atan = ATan

  FloatingSymReal ._**_ = Power
  FloatingSymReal .logBase x y = Div (Log y) (Log x)
  FloatingSymReal .sinh = Sinh
  FloatingSymReal .cosh = Cosh
  FloatingSymReal .tanh = Tanh
  FloatingSymReal .asinh = ASinh
  FloatingSymReal .acosh = ACosh
  FloatingSymReal .atanh = ATanh

  ArcTan2SymReal : ArcTan2-class SymReal
  ArcTan2SymReal .arctan2 y x = ArcTan2 y x

-- ----------------------------------------------------------------------
-- * Conversion to real number types

-- Evaluate a symbolic expression in a real number type. (Haskell's
-- errors, e.g. division by zero, follow the conventions of the
-- target type; for FixedPrec, see Data.Number.FixedPrec.)
to-real-SymReal : {R : Set} {{_ : RealTarget R}} -> SymReal -> R
to-real-SymReal (Const x) = fromℤ x
to-real-SymReal (Decimal x s) = fromℚ x
to-real-SymReal (Plus x y) = to-real-SymReal x + to-real-SymReal y
to-real-SymReal (Minus x y) = to-real-SymReal x - to-real-SymReal y
to-real-SymReal (Times x y) = to-real-SymReal x * to-real-SymReal y
to-real-SymReal (Negate x) = - to-real-SymReal x
to-real-SymReal (Abs x) = abs (to-real-SymReal x)
to-real-SymReal (Signum x) = signum (to-real-SymReal x)
to-real-SymReal (Div x y) = divide (to-real-SymReal x) (to-real-SymReal y)
to-real-SymReal (Recip x) = divide 1# (to-real-SymReal x)
to-real-SymReal Pi = π
to-real-SymReal Euler = exp 1#
to-real-SymReal (Exp x) = exp (to-real-SymReal x)
to-real-SymReal (Sqrt x) = sqrt (to-real-SymReal x)
to-real-SymReal (Log x) = log (to-real-SymReal x)
to-real-SymReal (Power x y) = to-real-SymReal x ** to-real-SymReal y
to-real-SymReal (Sin x) = sin (to-real-SymReal x)
to-real-SymReal (Tan x) = tan (to-real-SymReal x)
to-real-SymReal (Cos x) = cos (to-real-SymReal x)
to-real-SymReal (ASin x) = asin (to-real-SymReal x)
to-real-SymReal (ATan x) = atan (to-real-SymReal x)
to-real-SymReal (ACos x) = acos (to-real-SymReal x)
to-real-SymReal (Sinh x) = sinh (to-real-SymReal x)
to-real-SymReal (Tanh x) = tanh (to-real-SymReal x)
to-real-SymReal (Cosh x) = cosh (to-real-SymReal x)
to-real-SymReal (ASinh x) = asinh (to-real-SymReal x)
to-real-SymReal (ATanh x) = atanh (to-real-SymReal x)
to-real-SymReal (ACosh x) = acosh (to-real-SymReal x)
to-real-SymReal (ArcTan2 y x) = arctan2 (to-real-SymReal y) (to-real-SymReal x)

-- ----------------------------------------------------------------------
-- * A parser for real number expressions

-- The parser is a port of the ReadP grammar of the Haskell module.
-- Parsers return the list of all possible parses (like ReadP; the
-- grammar is unambiguous). The mutually recursive grammar functions
-- take fuel, which bounds the nesting depth; the top-level parser
-- gives fuel proportional to the length of the input, which is always
-- enough.
--
-- The parser uses simple precedences.
--
-- * Unary "+" and "−" have precedence 6.
-- * Binary "+" and "−" have precedence 6 and are left associative.
-- * Binary "*" and "/" have precedence 7 and are left associative.
-- * Binary "**" and "^" have precedence 8 and are right associative.
-- * All unary operators other than "+" and "−" have precedence 10.
--
-- We also allow whitespace between lexicographic entities.

module ReadP where
  Parser : Set -> Set
  Parser A = List Char -> List (A × List Char)

  infixl 1 _>>=_ _>>_
  infixr 3 _+++_

  return : {A : Set} -> A -> Parser A
  return a s = (a , s) ∷ []

  _>>=_ : {A B : Set} -> Parser A -> (A -> Parser B) -> Parser B
  (p >>= f) s = List.concatMap (λ { (a , s') -> f a s' }) (p s)

  _>>_ : {A B : Set} -> Parser A -> Parser B -> Parser B
  p >> q = p >>= λ _ -> q

  pfail : {A : Set} -> Parser A
  pfail s = []

  -- Symmetric choice.
  _+++_ : {A : Set} -> Parser A -> Parser A -> Parser A
  (p +++ q) s = p s List.++ q s

  choice : {A : Set} -> List (Parser A) -> Parser A
  choice = List.foldr _+++_ pfail

  option : {A : Set} -> A -> Parser A -> Parser A
  option x p = p +++ return x

  -- Zero or more repetitions (at most fuel many).
  many : {A : Set} -> ℕ -> Parser A -> Parser (List A)
  many zero p = return []
  many (suc f) p = return [] +++ (p >>= λ x -> many f p >>= λ xs -> return (x ∷ xs))

  sameChar : Char -> Char -> Bool
  sameChar c d = Char.toℕ c Nat.≡ᵇ Char.toℕ d

  char : Char -> Parser ⊤
  char c [] = []
  char c (d ∷ s) = if sameChar c d then (tt , s) ∷ [] else []

  string : String -> Parser ⊤
  string str = go (String.toList str)
    where
      go : List Char -> Parser ⊤
      go [] s = (tt , s) ∷ []
      go (c ∷ cs) [] = []
      go (c ∷ cs) (d ∷ s) = if sameChar c d then go cs s else []

  -- The longest prefix satisfying the predicate (greedy).
  munch : (Char -> Bool) -> Parser (List Char)
  munch p s = (List.takeWhileᵇ p s , List.dropWhileᵇ p s) ∷ []

  munch1 : (Char -> Bool) -> Parser (List Char)
  munch1 p s with List.takeWhileᵇ p s
  ... | [] = []
  ... | cs@(_ ∷ _) = (cs , List.dropWhileᵇ p s) ∷ []

  skipSpaces : Parser ⊤
  skipSpaces = munch Char.isSpace >> return tt

  eof : Parser ⊤
  eof [] = (tt , []) ∷ []
  eof (_ ∷ _) = []

open ReadP

-- The value of a string of decimal digits.
private
  digits-value : List Char -> ℕ
  digits-value = List.foldl (λ n c -> n Nat.* 10 Nat.+ (Char.toℕ c Nat.∸ Char.toℕ '0')) 0

-- ----------------------------------------------------------------------
-- ** Grammar specification

-- Each function in this section corresponds to a production rule for
-- a context-free grammar.

-- integer ::= digit digit*.
integer : Parser SymReal
integer = munch1 Char.isDigit >>= λ s -> return (Const (+ digits-value s))

-- float ::= digit* "." digit*.
--
-- There must be at least one digit, either before or after the
-- decimal point.
float : Parser SymReal
float =
  munch Char.isDigit >>= λ s1 ->
  char '.' >>
  munch Char.isDigit >>= λ s2 ->
  if List.null s1 ∧ List.null s2 then pfail
  else return (Decimal (rational s1 s2) (str s1 ++ "." ++ str s2))
  where
    rational : List Char -> List Char -> ℚ
    rational s1 s2 = + digits-value (s1 List.++ s2) Rat./ (10 Nat.^ List.length s2)
      where instance _ = NatP.m^n≢0 10 (List.length s2)
    str : List Char -> String
    str [] = "0"
    str s@(_ ∷ _) = String.fromList s

-- const-pi ::= "pi".
const-pi : Parser SymReal
const-pi = string "pi" >> return Pi

-- const-e ::= "e".
const-e : Parser SymReal
const-e = string "e" >> return Euler

-- negative ::= "−".
negative : Parser (SymReal -> SymReal)
negative = string "-" >> skipSpaces >> return Negate

-- positive ::= "+".
positive : Parser (SymReal -> SymReal)
positive = string "+" >> skipSpaces >> return id

-- unary-op ::= "abs" | "signum" | ...
unary-op : Parser (SymReal -> SymReal)
unary-op = choice (List.map (λ { (s , op) -> string s >> return op }) ops)
  where
    ops : List (String × (SymReal -> SymReal))
    ops = ("abs" , Abs) ∷ ("signum" , Signum) ∷ ("recip" , Recip) ∷
          ("exp" , Exp) ∷ ("sqrt" , Sqrt) ∷ ("log" , Log) ∷
          ("sin" , Sin) ∷ ("tan" , Tan) ∷ ("cos" , Cos) ∷
          ("asin" , ASin) ∷ ("atan" , ATan) ∷ ("acos" , ACos) ∷
          ("sinh" , Sinh) ∷ ("tanh" , Tanh) ∷ ("cosh" , Cosh) ∷
          ("asinh" , ASinh) ∷ ("atanh" , ATanh) ∷ ("acosh" , ACosh) ∷ []

-- binary-op ::= "arctan2".
binary-op : Parser (SymReal -> SymReal -> SymReal)
binary-op = string "arctan2" >> return ArcTan2

-- The mutually recursive part of the grammar. The first argument is
-- fuel (the maximal nesting depth).
mutual
  -- plus-term ::= "+" exp7.
  plus-term : ℕ -> Parser (SymReal -> SymReal)
  plus-term zero = pfail
  plus-term (suc f) =
    skipSpaces >> string "+" >> skipSpaces >> exp7 f >>= λ n2 -> return (λ n1 -> Plus n1 n2)

  -- minus-term ::= "−" exp7.
  minus-term : ℕ -> Parser (SymReal -> SymReal)
  minus-term zero = pfail
  minus-term (suc f) =
    skipSpaces >> string "-" >> skipSpaces >> exp7 f >>= λ n2 -> return (λ n1 -> Minus n1 n2)

  -- times-term ::= "*" exp8.
  times-term : ℕ -> Parser (SymReal -> SymReal)
  times-term zero = pfail
  times-term (suc f) =
    skipSpaces >> string "*" >> skipSpaces >> exp8 f >>= λ n2 -> return (λ n1 -> Times n1 n2)

  -- div-term ::= "/" exp8.
  div-term : ℕ -> Parser (SymReal -> SymReal)
  div-term zero = pfail
  div-term (suc f) =
    skipSpaces >> string "/" >> skipSpaces >> exp8 f >>= λ n2 -> return (λ n1 -> Div n1 n2)

  -- power-term ::= exp10 "**" | exp10 "^".
  power-term : ℕ -> Parser (SymReal -> SymReal)
  power-term zero = pfail
  power-term (suc f) =
    exp10 f >>= λ n1 -> skipSpaces >> (string "**" +++ string "^") >> skipSpaces >>
    return (λ n2 -> Power n1 n2)

  -- unary-fun ::= unary-op exp10.
  unary-fun : ℕ -> Parser SymReal
  unary-fun zero = pfail
  unary-fun (suc f) =
    skipSpaces >> unary-op >>= λ op -> skipSpaces >> exp10 f >>= λ n -> return (op n)

  -- binary-fun ::= binary-op exp10 exp10.
  binary-fun : ℕ -> Parser SymReal
  binary-fun zero = pfail
  binary-fun (suc f) =
    skipSpaces >> binary-op >>= λ op -> skipSpaces >> exp10 f >>= λ n ->
    skipSpaces >> exp10 f >>= λ m -> return (op n m)

  -- exp6 ::= (negative | positive)? exp7 ( plus-term | minus-term )*.
  --
  -- An expression whose top-level operator has precedence 6 or above.
  exp6 : ℕ -> Parser SymReal
  exp6 zero = pfail
  exp6 (suc f) =
    option id (negative +++ positive) >>= λ sign ->
    exp7 f >>= λ n1 ->
    many f (plus-term f +++ minus-term f) >>= λ ops ->
    return (List.foldl (λ x g -> g x) (sign n1) ops)

  -- exp7 ::= exp8 ( times-term | div-term )*.
  --
  -- An expression whose top-level operator has precedence 7 or above.
  exp7 : ℕ -> Parser SymReal
  exp7 zero = pfail
  exp7 (suc f) =
    exp8 f >>= λ n1 ->
    many f (times-term f +++ div-term f) >>= λ ops ->
    return (List.foldl (λ x g -> g x) n1 ops)

  -- exp8 ::= ( power-term )* exp10.
  --
  -- An expression whose top-level operator has precedence 8 or above.
  exp8 : ℕ -> Parser SymReal
  exp8 zero = pfail
  exp8 (suc f) =
    many f (power-term f) >>= λ ops ->
    exp10 f >>= λ n2 ->
    return (List.foldr (λ g x -> g x) n2 ops)

  -- exp10 ::= parenthesized | const-pi | const-e | integer | float
  --         | unary-fun | binary-fun.
  --
  -- An expression whose top-level operator has precedence 10 or
  -- above: constants, applications of unary operators (except unary
  -- "−" and "+"), and parenthesized expressions.
  exp10 : ℕ -> Parser SymReal
  exp10 zero = pfail
  exp10 (suc f) =
    parenthesized f +++ const-pi +++ const-e +++ integer +++ float +++ unary-fun f +++ binary-fun f

  -- parenthesized ::= "(" exp6 ")".
  parenthesized : ℕ -> Parser SymReal
  parenthesized zero = pfail
  parenthesized (suc f) =
    string "(" >> skipSpaces >> exp6 f >>= λ n -> skipSpaces >> string ")" >> return n

-- expression ::= exp6 end-of-line.
--
-- This is a top-level expression.
expression : ℕ -> Parser SymReal
expression f = skipSpaces >> exp6 f >>= λ s -> skipSpaces >> eof >> return s

-- ----------------------------------------------------------------------
-- ** Top-level parser

-- Parse a symbolic real number expression. Typical strings that can
-- be parsed are "1.0", "pi/128", "(1+sin(pi/3))^2", etc. If the
-- expression cannot be parsed, return nothing. (Note that exponent
-- notation such as "1e-3" is not supported: "e" is Euler's number.)
parse-SymReal : String -> Maybe SymReal
parse-SymReal str with expression fuel cs
  where
    cs = String.toList str
    fuel = (List.length cs Nat.+ 2) Nat.* 10
... | (h , []) ∷ _ = just h
... | _ = nothing

-- ToReal instances for SymReal and String.
instance
  ToRealSymReal : ToReal SymReal
  ToRealSymReal .to-real = to-real-SymReal

  -- A string that does not parse (Haskell: error) gives 0.
  ToRealString : ToReal String
  ToRealString .to-real s with parse-SymReal s
  ... | just x = to-real-SymReal x
  ... | nothing = 0#
