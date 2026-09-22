-- Sanity checks for Quantum.Synthesis.CliffordT, checked by
-- evaluation. Expected values agree with the Haskell reference
-- implementation newsynth-0.4.1.0. (See Test/CliffordTRun.agda and
-- Test/CliffordTRun2.agda for compiled tests: synthesis round trips
-- and many more comparisons with Haskell.)

{-# OPTIONS --without-K --safe #-}

module Test.CliffordT where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Integer.Base using (ℤ)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (just ; nothing)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Function.Base using (_∋_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.Clifford
open import Quantum.Synthesis.CliffordT

-- Identities between the U(2) matrices.
_ : (U2 DOmega ∋ u2-H * u2-H) ≡ 1
_ = refl
_ : (U2 DOmega ∋ u2-T ^ 2) ≡ u2-S
_ = refl
_ : (U2 DOmega ∋ u2-T ^ 4) ≡ u2-Z
_ = refl
_ : (U2 DOmega ∋ u2-T ^ 4 * u2-T ^ 4) ≡ 1
_ = refl
_ : (U2 DOmega ∋ u2-S * u2-S) ≡ u2-Z
_ = refl
_ : (U2 DOmega ∋ u2-X * u2-Z) ≡ - i * u2-Y
_ = refl
_ : (U2 DOmega ∋ u2-W ^ 4) ≡ -1
_ = refl
_ : (U2 DOmega ∋ u2-E * u2-E * u2-E) ≡ 1
_ = refl
_ : (U2 DOmega ∋ u2-H * u2-S ^ 3 * u2-W ^ 3) ≡ u2-E
_ = refl
_ : (U2 DRComplex ∋ from-gates (H ∷ H ∷ [])) ≡ 1
_ = refl

-- Identities between the SO(3) matrices.
_ : (SO3 DRootTwo ∋ so3-T * so3-T) ≡ so3-S
_ = refl
_ : (SO3 ZRootTwo ∋ so3-E * so3-E * so3-E) ≡ 1
_ = refl
_ : (SO3 DRootTwo ∋ so3-of-u2 (U2 DOmega ∋ u2-H)) ≡ so3-H
_ = refl
_ : (SO3 ZRootTwo ∋ so3-of-clifford "SH") ≡ so3-S * so3-H
_ = refl
_ : clifford-of-so3 (SO3 ZRootTwo ∋ so3-of-clifford "SH") ≡ to-clifford "SH"
_ = refl

-- Gate lists and normal forms.
_ : to-gates "HT-iI" ≡ H ∷ T ∷ W ∷ W ∷ W ∷ W ∷ W ∷ W ∷ []
_ = refl
_ : invert-gates (S ∷ T ∷ E ∷ W ∷ []) ≡ W ∷ W ∷ W ∷ W ∷ W ∷ W ∷ W ∷ E ∷ E ∷ Z ∷ S ∷ T ∷ Z ∷ S ∷ []
_ = refl
_ : (String ∋ convert "HTSHT") ≡ "HTSHT"
_ = refl
_ : normalize "HH" ≡ nf-id
_ = refl
_ : show (normalize (H ∷ T ∷ [])) ≡ "HT"
_ = refl
_ : show (normalize "HTTSHXW") ≡ "W"
_ = refl
_ : show (normalize (List Gate ∋ [])) ≡ "I"
_ = refl
_ : show (normalize (H ∷ T ∷ H ∷ S ∷ T ∷ [])) ≡ "HTHTS"
_ = refl
_ : show (normalize (T ∷ H ∷ T ∷ S ∷ H ∷ T ∷ [])) ≡ "THTSHT"
_ = refl
_ : nf-mult (normalize "THT") (nf-inv "THT") ≡ nf-id
_ = refl
_ : show (SApp-SHT (SApp-HT S-T)) ≡ "SApp_SHT (SApp_HT S_T)"
_ = refl

-- Packing.
_ : normalform-pack (normalize (T ∷ H ∷ T ∷ S ∷ H ∷ T ∷ [])) ≡ 3328
_ = refl
_ : normalform-unpack 3328 ≡ just (normalize (T ∷ H ∷ T ∷ S ∷ H ∷ T ∷ []))
_ = refl
_ : normalform-unpack 700 ≡ nothing
_ = refl
_ : (ℤ ∋ from-gates (H ∷ T ∷ S ∷ H ∷ T ∷ E ∷ [])) ≡ 2395
_ = refl
_ : clifford-unpack 100 ≡ just (Clifford' 1 1 3 3)
_ = refl
_ : clifford-unpack 192 ≡ nothing
_ = refl

-- Exact synthesis (Haskell: synthesis_u2 (from_gates [H,T,H]) = [H,T,H]).
_ : synthesis-u2 (from-gates (H ∷ T ∷ H ∷ [])) ≡ H ∷ T ∷ H ∷ []
_ = refl
_ : synthesis-bloch (from-gates (H ∷ T ∷ [])) ≡ H ∷ T ∷ []
_ = refl
