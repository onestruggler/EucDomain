-- Sanity checks for Quantum.Synthesis.MultiQubitSynthesis, checked by
-- evaluation. Expected values agree with the Haskell reference
-- implementation newsynth-0.4.1.0. (See Test/CliffordTRun2.agda for
-- compiled tests of the synthesis of larger operators.)

{-# OPTIONS --without-K --safe #-}

module Test.MultiQubitSynthesis where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.List.Base using (List ; [] ; _∷_)
import Data.Bool.Base
import Data.Nat.Base
open import Data.Maybe.Base using (just ; nothing)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∋_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.MultiQubitSynthesis

-- Residues.
_ : residue (ZOmega ∋ Omega 1 2 3 4) ≡ Omega Odd Even Odd Even
_ = refl
_ : residue-type-shift (Omega Even Odd Odd Odd) ≡ (RT-0001 , 3)
_ = refl
_ : reducible (Omega Odd Even Odd Even) ≡ Data.Bool.Base.true
_ = refl
_ : residue-offset (Omega Even Even Even Odd) (Omega Even Odd Even Even) ≡ 2
_ = refl

-- Functions on ℤ[ω].
_ : log-omega (ω ^ 5) ≡ just 5
_ = refl
_ : log-omega (1 + ω) ≡ nothing
_ = refl
_ : reduce-ZOmega (roottwo * (1 + ω)) ≡ Omega 0 0 1 1
_ = refl
_ : omega-power -1 (ZOmega ∋ ω) ≡ 1
_ = refl
_ : apply-twolevels-zomega (TL-H 0 1 ∷ []) (1 + ω ∷ 1 - ω ∷ []) ≡ roottwo ∷ roottwo * ω ∷ []
_ = refl

-- List functions.
_ : list-pairs (List Data.Nat.Base.ℕ ∋ 1 ∷ 2 ∷ 3 ∷ []) ≡ ((1 , 2) ∷ [] , just 3)
_ = refl
_ : transform-at2 (λ { (x , y) -> (y , x) }) 0 2 (List Data.Nat.Base.ℕ ∋ 1 ∷ 2 ∷ 3 ∷ []) ≡ 3 ∷ 2 ∷ 1 ∷ []
_ = refl

-- Two-level operators.
_ : invert-twolevels (TL-T 3 0 1 ∷ TL-H 0 1 ∷ TL-omega -1 1 ∷ []) ≡ TL-omega 1 1 ∷ TL-H 0 1 ∷ TL-T -3 0 1 ∷ []
_ = refl
_ : (Matrix Three Three DOmega ∋ matrix-of-twolevel (TL-X 0 2)) ≡ matrix3x3 (0 , 0 , 1) (0 , 1 , 0) (1 , 0 , 0)
_ = refl
_ : (U2 DOmega ∋ matrix-of-twolevels (TL-T 1 0 1 ∷ TL-T 1 0 1 ∷ [])) ≡ matrix2x2 (1 , 0) (0 , i)
_ = refl
_ : twolevels-of-twolevelalts (TL-W 1 0 1 ∷ []) ≡ TL-omega 1 0 ∷ TL-omega -1 1 ∷ []
_ = refl
_ : show (TL-T -1 0 1) ≡ "TL_T (-1) 0 1"
_ = refl
_ : show (TL-omega-alt 7 1) ≡ "TL_omega_alt 7 1"
_ = refl

-- Exact synthesis of the Hadamard gate (Haskell:
-- [TL_H 0 1,TL_omega 0 0,TL_omega 0 1]).
_ : synthesis-nqubit (U2 DOmega ∋ roothalf * matrix2x2 (1 , 1) (1 , -1)) ≡ TL-H 0 1 ∷ TL-omega 0 0 ∷ TL-omega 0 1 ∷ []
_ = refl
