-- Sanity checks for Quantum.Synthesis.Clifford, checked by
-- evaluation. Expected values agree with the Haskell reference
-- implementation newsynth-0.4.1.0.

{-# OPTIONS --without-K --safe #-}

module Test.Clifford where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Product.Base using (_,_)

open import Instances
open import Literals
open import Quantum.Synthesis.Clifford

-- Group laws.
_ : clifford-mult clifford-H clifford-H ≡ clifford-id
_ = refl
_ : to-clifford "EEE" ≡ clifford-id
_ = refl
_ : to-clifford "SSSS" ≡ clifford-id
_ = refl
_ : to-clifford "WWWWWWWW" ≡ clifford-id
_ = refl
_ : to-clifford "SS" ≡ clifford-Z
_ = refl
_ : to-clifford "HSSSWWW" ≡ clifford-E
_ = refl
_ : clifford-mult (clifford-inv "HSE") (to-clifford "HSE") ≡ clifford-id
_ = refl
_ : to-clifford "-i" ≡ Clifford' 0 0 0 6
_ = refl

-- The E conjugation properties: EXE⁻¹ = Y, EYE⁻¹ = Z, EZE⁻¹ = X.
_ : clifford-mult (to-clifford "EX") (clifford-inv "E") ≡ clifford-Y
_ = refl
_ : clifford-mult (to-clifford "EY") (clifford-inv "E") ≡ clifford-Z
_ = refl
_ : clifford-mult (to-clifford "EZ") (clifford-inv "E") ≡ clifford-X
_ = refl

-- Decompositions (compared with Haskell).
_ : to-clifford "HSSHX" ≡ clifford-id
_ = refl
_ : clifford-decompose "SH" ≡ (2 , 0 , 0 , 3)
_ = refl
_ : clifford-decompose-coset "HSS" ≡ (Axis-H , 0 , 2 , 0)
_ = refl
_ : clifford-tconj (to-clifford "HS") ≡ (Axis-H , Clifford' 0 0 1 0)
_ = refl
_ : clifford-inv "HSE" ≡ Clifford' 1 1 0 3
_ = refl

-- Printing.
_ : show clifford-H ≡ "C1015"
_ = refl
_ : show clifford-SH ≡ "C2003"
_ = refl
_ : show Axis-SH ≡ "Axis_SH"
_ = refl
