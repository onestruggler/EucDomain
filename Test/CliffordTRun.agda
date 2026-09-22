{-# OPTIONS --guardedness #-}
-- Compiled tests for Quantum.Synthesis.Matrix, Clifford,
-- MultiQubitSynthesis and CliffordT. The expected output (from the
-- Haskell reference implementation newsynth-0.4.1.0) was obtained
-- by evaluating the corresponding Haskell expressions; each line of
-- output here matched the Haskell output line by line.
module Test.CliffordTRun where

open import IO
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base using (ℤ)
open import Data.Float.Base using (Float)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.String.Base as String using (String ; _++_)
open import Function.Base using (_∋_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.Clifford
open import Quantum.Synthesis.MultiQubitSynthesis
open import Quantum.Synthesis.CliffordT

showL : {A : Set} {{_ : Show A}} -> List A -> String
showL = showList showsPrec

showM : {A : Set} {{_ : Show A}} -> Maybe A -> String
showM (just x) = show x
showM nothing = "error"

showB : Bool -> String
showB true = "True"
showB false = "False"

u2 : List Gate -> U2 DOmega
u2 = from-gates

so3 : List Gate -> SO3 DRootTwo
so3 = from-gates

gs1 : List Gate
gs1 = T ∷ H ∷ T ∷ S ∷ H ∷ T ∷ W ∷ []

-- 0x6bf723e31
code : ℤ
code = 28981739057

lines : List String
lines =
  show (U2 DOmega ∋ u2-of-gate H) ∷
  show (U2 DOmega ∋ u2-of-gate E) ∷
  show ((U2 DOmega ∋ u2-of-gate T) ^ 8) ∷
  show (u2 (H ∷ T ∷ S ∷ H ∷ T ∷ [])) ∷
  show (SO3 DRootTwo ∋ so3-of-gate T) ∷
  show (so3 (H ∷ T ∷ S ∷ H ∷ T ∷ [])) ∷
  show (so3-of-u2 {B = DRootTwo} (u2 (H ∷ T ∷ []))) ∷
  showL (synthesis-u2 (u2 (H ∷ T ∷ S ∷ H ∷ T ∷ H ∷ T ∷ E ∷ W ∷ W ∷ Y ∷ []))) ∷
  showL (synthesis-bloch (so3 (H ∷ T ∷ S ∷ H ∷ T ∷ H ∷ T ∷ E ∷ Y ∷ []))) ∷
  show (normalize (H ∷ T ∷ S ∷ H ∷ T ∷ H ∷ T ∷ E ∷ W ∷ Y ∷ [])) ∷
  show (normalform-pack (normalize (T ∷ H ∷ T ∷ S ∷ H ∷ T ∷ []))) ∷
  showM (normalform-unpack code) ∷
  show (clifford-of-so3 (SO3 ZRootTwo ∋ so3-of-clifford "SH")) ∷
  showList (λ _ n -> showM (clifford-unpack n)) (0 ∷ 17 ∷ 100 ∷ 191 ∷ []) ∷
  show (to-clifford "HSSHX") ∷
  (case-coset (clifford-decompose-coset "HSS")) ∷
  (case-tconj (clifford-tconj (to-clifford "HS"))) ∷
  show (clifford-inv "HSE") ∷
  showL (synthesis-nqubit (u2 (H ∷ T ∷ S ∷ []))) ∷
  showL (synthesis-nqubit-alt (u2 (H ∷ T ∷ S ∷ []))) ∷
  showL (synthesis-nqubit (Matrix Four Four DOmega ∋ cnot * tensor (u2-of-gate H) (u2-of-gate T))) ∷
  showL (synthesis-nqubit-alt (Matrix Four Four DOmega ∋ cnot * tensor (u2-of-gate H) (u2-of-gate T))) ∷
  showL (invert-gates (S ∷ T ∷ E ∷ W ∷ [])) ∷
  (String ∋ convert "HTSHT") ∷
  (String ∋ convert code) ∷
  show (Matrix Three Three DOmega ∋ matrix-of-twolevels (TL-H 0 1 ∷ TL-T 3 1 2 ∷ TL-omega -1 0 ∷ [])) ∷
  show (zrot {Float} 0.5) ∷
  show (tensor (U2 DOmega ∋ u2-of-gate H) (u2-of-gate T)) ∷
  show (hs-sqnorm (U2 DRComplex ∋ u2-of-gate H)) ∷
  show (Matrix Four Four ℤ ∋ cnot) ∷
  show (Matrix Four Four DOmega ∋ matrix-controlled (u2-of-gate X)) ∷
  show (U2 DRComplex ∋ u2-of-gate H) ∷
  show (SO3 DRootTwo ∋ so3-of-gate H) ∷
  showL (TL-T -1 0 1 ∷ TL-omega 3 0 ∷ TL-X 0 1 ∷ []) ∷
  show (normalform-pack (normalize code)) ∷
  show (ℤ ∋ from-gates (H ∷ T ∷ S ∷ H ∷ T ∷ E ∷ [])) ∷
  show (normalize "HTTSHXW") ∷
  showL (to-gates (SO3 DRootTwo ∋ so3-of-u2 (u2 (T ∷ H ∷ T ∷ S ∷ H ∷ T ∷ [])))) ∷
  showL (to-gates (u2 gs1)) ∷
  showB (matrix-of-twolevels (synthesis-nqubit (u2 gs1)) == u2 gs1) ∷
  show (normalize (Y ∷ [])) ∷
  show (normalize (List Gate ∋ [])) ∷
  ("\"" ++ show (normalize (H ∷ T ∷ H ∷ S ∷ T ∷ [])) ++ "\"") ∷
  showL (clifford-X ∷ clifford-Y ∷ clifford-Z ∷ clifford-H ∷ clifford-S ∷ clifford-SH ∷ clifford-E ∷ clifford-W ∷ []) ∷
  show (denomexp (u2 (H ∷ T ∷ S ∷ H ∷ T ∷ []))) ∷
  show (U2 DRComplex ∋ u2-of-gate T) ∷
  []
  where
    case-coset : Axis × ℕ × ℕ × ℕ -> String
    case-coset (k , b , c , d) = "(" ++ show k ++ "," ++ show b ++ "," ++ show c ++ "," ++ show d ++ ")"
    case-tconj : Axis × Clifford -> String
    case-tconj (k , c) = "(" ++ show k ++ "," ++ show c ++ ")"

main : Main
main = run (List.foldr (λ s io -> putStrLn s >> io) (pure _) lines)
