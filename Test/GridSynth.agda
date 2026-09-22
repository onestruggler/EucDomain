{-# OPTIONS --guardedness #-}
-- Tests (by refl) of Quantum.Synthesis.GridSynth and of the helper
-- modules of the gridsynth program (Programs.GetOpt,
-- Programs.CommandLine, Programs.Gridsynth). The algorithm itself is
-- tested by the compiled test Test.GridSynthRun and the comparison
-- script Test/gridsynth-compare.sh.
module Test.GridSynth where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Char.Base using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
open import Data.Product.Base using (_×_ ; _,_)
open import Data.String.Base using (String)
import Data.String.Base
open import Data.Float.Base as Float using (Float)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Literals
open import Quantum.Synthesis.Random using (StdGen')
open import Quantum.Synthesis.GridSynth
open import Programs.GetOpt
open import Programs.CommandLine
open import Programs.Gridsynth

-- ----------------------------------------------------------------------
-- GridSynth auxiliaries

cmp : ℕ -> ℕ -> Ordering
cmp m n = if m Nat.<ᵇ n then LT else if n Nat.<ᵇ m then GT else EQ
  where open import Data.Bool.Base using (if_then_else_)

_ : mergeBy cmp (1 ∷ 4 ∷ 6 ∷ []) (2 ∷ 3 ∷ 5 ∷ 7 ∷ 8 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []
_ = refl

-- ties are taken from the second list first (as in Haskell)
_ : mergeBy (λ (x y : ℕ × ℕ) -> cmp (Data.Product.Base.proj₁ x) (Data.Product.Base.proj₁ y))
      ((1 , 0) ∷ []) ((1 , 1) ∷ []) ≡ (1 , 1) ∷ (1 , 0) ∷ []
_ = refl

_ : first {ℕ} {Bool} {String} (3 , true , "x") ≡ 3
_ = refl

_ : show Success ≡ "Success"
_ = refl

_ : (Timeout == Fail) ≡ false
_ = refl

-- ----------------------------------------------------------------------
-- CommandLine

_ : string-of-list "{" ", " "}" "{}" (show {ℕ}) (1 ∷ 2 ∷ 3 ∷ []) ≡ "{1, 2, 3}"
_ = refl

_ : string-of-list "{" ", " "}" "{}" (show {ℕ}) [] ≡ "{}"
_ = refl

_ : parse-int "42" ≡ just (+ 42)
_ = refl

_ : parse-int " ( - 0x1F )" ≡ just (Int.- (+ 31))
_ = refl

_ : parse-int "1e3" ≡ nothing
_ = refl

_ : parse-int "12 " ≡ nothing
_ = refl

_ : parse-list-int "[1, -2 ,(3)]" ≡ just (+ 1 ∷ Int.- (+ 2) ∷ + 3 ∷ [])
_ = refl

_ : parse-list-int "[]" ≡ just []
_ = refl

_ : parse-list-int "[,]" ≡ nothing
_ = refl

_ : to-int64 (+ 9223372036854775808) ≡ Int.- (+ 9223372036854775808)
_ = refl

_ : parse-double "1e1" ≡ just 10.0
_ = refl

_ : parse-double "(2.5)" ≡ just 2.5
_ = refl

_ : parse-double "- 0.25e-1" ≡ just (-0.025)
_ = refl

_ : parse-double "0o17" ≡ just 15.0
_ = refl

_ : parse-double "1." ≡ nothing
_ = refl

_ : parse-double ".5" ≡ nothing
_ = refl

_ : parse-double "1e99999999999999999999" ≡ just (1.0 Float.÷ 0.0)
_ = refl

enum1 enum2 : List (String × ℕ)
enum1 = ("foo" , 1) ∷ ("bar" , 2) ∷ ("baz" , 3) ∷ []
enum2 = ("foo" , 1) ∷ ("foobar" , 2) ∷ []

_ : match-enum enum1 "BA" ≡ ("bar" , 2) ∷ ("baz" , 3) ∷ []
_ = refl

_ : match-enum enum2 "Foo" ≡ ("foo" , 1) ∷ []
_ = refl

_ : show-enum "x" enum2 ≡ "Possible values for x are: foo, foobar.\n"
_ = refl

-- ----------------------------------------------------------------------
-- GetOpt

private
  opts : List (OptDescr String)
  opts = Option' ('v' ∷ []) ("verbose" ∷ []) (NoArg "v") "be verbose" ∷
         Option' ('n' ∷ []) ("number" ∷ "num" ∷ []) (ReqArg (λ s -> "n=" Data.String.Base.++ s) "<n>") "a number" ∷
         Option' ('o' ∷ []) ("output" ∷ []) (OptArg (λ { nothing -> "o" ; (just s) -> "o=" Data.String.Base.++ s }) "FILE") "output" ∷
         []

_ : getOpt Permute opts ("-vn3" ∷ "x" ∷ "--num=4" ∷ "--out" ∷ "-oF" ∷ "--" ∷ "-v" ∷ [])
    ≡ ("v" ∷ "n=3" ∷ "n=4" ∷ "o" ∷ "o=F" ∷ [] , "x" ∷ "-v" ∷ [] , [])
_ = refl

_ : getOpt RequireOrder opts ("-v" ∷ "x" ∷ "-v" ∷ []) ≡ ("v" ∷ [] , "x" ∷ "-v" ∷ [] , [])
_ = refl

_ : getOpt Permute opts ("-z" ∷ "--verbose=1" ∷ "-n" ∷ []) ≡
    ([] , [] , "option `--verbose' doesn't allow an argument\n" ∷ "option `-n' requires an argument <n>\n" ∷
               "unrecognized option `-z'\n" ∷ [])
_ = refl

_ : usageInfo "Usage:" opts ≡
    "Usage:\n  -v        --verbose                be verbose\n  -n <n>    --number=<n>, --num=<n>  a number\n  -o[FILE]  --output[=FILE]          output\n"
_ = refl

-- ----------------------------------------------------------------------
-- The gridsynth program

_ : parse-rseed "1" ≡ just (StdGen' (+ 53) (+ 1))
_ = refl

_ : parse-rseed " 12  34" ≡ just (StdGen' (+ 12) (+ 34))
_ = refl

_ : parse-rseed "12 34 " ≡ nothing
_ = refl

_ : parse-rseed "1234567" ≡ nothing
_ = refl

_ : parse-rseed "4294967298 1" ≡ just (StdGen' (+ 2) (+ 1))
_ = refl

_ : show-time 20797535000 ≡ "0.020797535s"
_ = refl

_ : show-time 3000000000000 ≡ "3s"
_ = refl

_ : show-time 2000100000 ≡ "0.0020001s"
_ = refl

_ : show-exp 10 (+ 10) (just 10.0) ≡ "10^(-10)"
_ = refl

_ : show-exp 10 (+ 3) nothing ≡ "0.0000000000*10^(-3)"
_ = refl

_ : showlatex-exp 5 (+ 2) (just 2.5) ≡ "0.31623\\cdot 10^{-2}"
_ = refl

_ : round-to 0 2.5 ≡ 2.0
_ = refl

_ : round-to 0 3.5 ≡ 4.0
_ = refl

_ : round-to 0 (-2.5) ≡ -2.0
_ = refl

_ : parse-double "1e-99999999999999999999" ≡ just 0.0
_ = refl

_ : parse-rseed "(1)" ≡ just (StdGen' (+ 576) (+ 1))
_ = refl
