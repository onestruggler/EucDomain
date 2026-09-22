{-# OPTIONS --guardedness #-}
-- More compiled tests for Quantum.Synthesis.Clifford,
-- MultiQubitSynthesis and CliffordT: synthesis of many operators
-- (given by their packed normal forms), the Clifford group tables,
-- and multi-qubit synthesis of 4×4 and 8×8 operators. The output
-- was compared line by line with the Haskell reference
-- implementation newsynth-0.4.1.0.
module Test.CliffordTRun2 where

open import IO
import Data.Bool.Base
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Integer.Base as Int using (ℤ ; +_)
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

-- [from, from+step, ..., ≤ to] (Haskell's enumFromThenTo).
range : ℕ -> ℕ -> ℕ -> List ℕ
range from step to = List.filterᵇ (λ n -> n Nat.≤ᵇ to) (List.map (λ k -> from Nat.+ k Nat.* step) (List.upTo (Nat.suc to)))

-- [256*s + c | s <- [s0, s0+ds .. s1], c <- [c0, c0+dc .. 191]]
codes : ℕ -> ℕ -> ℕ -> ℕ -> ℕ -> List ℤ
codes s0 ds s1 c0 dc = List.concatMap (λ s -> List.map (λ c -> + (256 Nat.* s Nat.+ c)) (range c0 dc 191)) (range s0 ds s1)

cl : ℕ -> Clifford
cl n with clifford-unpack (+ n)
... | just c = c
... | nothing = clifford-id

u2 : List Gate -> U2 DOmega
u2 = from-gates

so3 : List Gate -> SO3 DRootTwo
so3 = from-gates

showB : Data.Bool.Base.Bool -> String
showB Data.Bool.Base.true = "True"
showB Data.Bool.Base.false = "False"

m4 : Matrix Four Four DOmega
m4 = tensor (u2 (H ∷ T ∷ S ∷ H ∷ T ∷ [])) (u2 (T ∷ H ∷ E ∷ [])) * cnot

m8 : Matrix Eight Eight DOmega
m8 = matrix-controlled (cnot * tensor (U2 DOmega ∋ u2-of-gate H) (u2 (T ∷ H ∷ T ∷ S ∷ H ∷ T ∷ [])))

lines : List String
lines =
  showL (List.map (λ n -> ℤ ∋ from-gates (synthesis-u2 (from-gates (to-gates n)))) (codes 3 3 120 0 37)) ∷
  showL (List.map (λ n -> ℤ ∋ from-gates (synthesis-bloch (from-gates (to-gates n)))) (codes 3 3 120 0 37)) ∷
  showL (List.concatMap (λ a -> List.map (λ b -> clifford-mult (cl a) (cl b)) (range 0 11 191)) (range 0 7 191)) ∷
  showL (List.map (λ n -> clifford-of-so3 (SO3 ZRootTwo ∋ so3-of-clifford (cl n))) (range 0 1 191)) ∷
  showL (List.map (λ n -> clifford-inv (cl n)) (range 0 1 191)) ∷
  showList (λ _ p -> tc p) (List.map (λ n -> clifford-tconj (cl n)) (range 0 5 191)) ∷
  showL (synthesis-nqubit m4) ∷
  showL (synthesis-nqubit-alt m4) ∷
  showL (synthesis-nqubit m8) ∷
  showL (synthesis-nqubit-alt m8) ∷
  showList (λ _ n -> showM (normalform-unpack n)) (codes 3 5 300 3 38) ∷
  -- Round trips: gate list → matrix → synthesized gates → matrix.
  showB (List.all (λ n -> u2 (synthesis-u2 (u2 (to-gates n))) == u2 (to-gates n)) (codes 3 3 120 0 37)) ∷
  showB (List.all (λ n -> so3 (synthesis-bloch (so3 (to-gates n))) == so3 (to-gates n)) (codes 3 3 120 0 37)) ∷
  []
  where
    tc : Axis × Clifford -> String
    tc (k , c) = "(" ++ show k ++ "," ++ show c ++ ")"

main : Main
main = run (List.foldr (λ s io -> putStrLn s >> io) (pure _) lines)
