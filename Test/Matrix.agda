-- Sanity checks for Quantum.Synthesis.Matrix, checked by evaluation.
-- Expected strings were obtained from the Haskell reference
-- implementation newsynth-0.4.1.0.

{-# OPTIONS --without-K --safe #-}

module Test.Matrix where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Integer.Base using (ℤ)
open import Data.Empty using (⊥)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([] ; _∷_)
open import Function.Base using (_∋_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Test.Ring using (FourBase ; inverse-one-plus-omega)
import Quantum.Synthesis.Matrix.Properties as MP
import Quantum.Synthesis.Ring.Properties as RP
import Quantum.Synthesis.Ring.Properties.DyadicComplex as DC

private
  module ZLinear = MP.Linear {R = ZComplex} {{RingCplx}} RP.isCommutativeRing-ZComplex
  module ZConjugate = ZLinear.Conjugate RP.adj-ZComplex
  module Embed = MP.Map {A = ZComplex} {B = DComplex} {{RingCplx}} {{RingCplx}}
    RP.isCommutativeRing-ZComplex RP.isCommutativeRing-DComplex DC.embed-isRingHom

  upper diagonal : Matrix 2 2 ZComplex
  upper = matrix2x2 (0 , 1) (0 , 0)
  diagonal = matrix2x2 (1 , 0) (0 , 0)

  emptyLeft : Matrix 2 0 ZComplex
  emptyLeft = Matrix' []
  emptyRight : Matrix 0 3 ZComplex
  emptyRight = Matrix' ([] ∷ [] ∷ [] ∷ [])

-- Scalar adj is multiplicative; native matrix adjoint reverses the order.
_ : adjoint (upper ·*· diagonal) ≡ adjoint diagonal ·*· adjoint upper
_ = ZConjugate.†-* upper diagonal

_ : adjoint (upper ·*· diagonal) ≡ adjoint upper ·*· adjoint diagonal → ⊥
_ = λ ()

-- The empty inner dimension must still preserve the additive zero.
_ : (Matrix' [] ·*· Matrix' ([] ∷ [] ∷ [] ∷ [])) ≡ (Matrix 2 3 DComplex ∋ null-matrix)
_ = refl

_ : matrix-map DC.embed (emptyLeft ·*· emptyRight) ≡
  matrix-map DC.embed emptyLeft ·*· matrix-map DC.embed emptyRight
_ = Embed.map-product emptyLeft emptyRight

-- Base selection propagates through vectors and rectangular matrices.
denominator-example : Matrix 2 3 DRootTwo
denominator-example = Matrix'
  ((½ ∷ 0 ∷ []) ∷ (√½ ∷ 1 ∷ []) ∷ (½ ^ 3 ∷ (- ½) ∷ []) ∷ [])

_ : denomexp denominator-example ≡ 6
_ = refl
_ : denomexpBy TwoBase denominator-example ≡ 3
_ = refl
_ : denomexp-decomposeBy {Matrix 2 3 DRootTwo} {Matrix 2 3 ZRootTwo}
      TwoBase denominator-example ≡
      (Matrix' ((4 ∷ 0 ∷ []) ∷ (4 * √2 ∷ 8 ∷ []) ∷ (1 ∷ -4 ∷ []) ∷ []) , 3)
_ = refl
_ : denomexpBy TwoBase (Matrix 0 2 Dyadic ∋ Matrix' ([] ∷ [] ∷ [])) ≡ 0
_ = refl
_ : denomexpBy FourBase (Matrix 2 0 Dyadic ∋ Matrix' []) ≡ 0
_ = refl
_ : denomexp-decomposeBy {Vector 2 Dyadic} {Vector 2 ℤ} FourBase
      (½ ∷ dyadic 1 3 ∷ []) ≡ ((8 ∷ 2 ∷ []) , 2)
_ = refl
_ : denomexp-decomposeBy {Matrix 1 1 Dyadic} {Matrix 1 1 ℤ} FourBase
      (Matrix' ((dyadic 1 3 ∷ []) ∷ [])) ≡ (Matrix' ((2 ∷ []) ∷ []) , 2)
_ = refl

-- Complex bases act by multiplication, mixing scalar coordinates while
-- the matrix instance still selects the maximum entry exponent.
_ : denomexp-decomposeBy {Matrix 1 2 DComplex} {Matrix 1 2 ZComplex} OnePlusIBase
      (Matrix' ((½ * (1 - i) ∷ []) ∷ (½ ∷ []) ∷ [])) ≡
      (Matrix' ((1 + i ∷ []) ∷ (i ∷ []) ∷ []) , 2)
_ = refl
_ : denomexp-decomposeBy {Matrix 2 1 DOmega} {Matrix 2 1 ZOmega} OnePlusOmegaBase
      (Matrix' ((inverse-one-plus-omega ∷ inverse-one-plus-omega ^ 3 ∷ []) ∷ [])) ≡
      (Matrix' (((1 + ω) ^ 2 ∷ 1 ∷ []) ∷ []) , 3)
_ = refl
_ : denomexpBy OnePlusIBase (Matrix 0 2 DComplex ∋ Matrix' ([] ∷ [] ∷ [])) ≡ 0
_ = refl
_ : denomexpBy OnePlusOmegaBase (Matrix 2 0 DOmega ∋ Matrix' []) ≡ 0
_ = refl

A B : Matrix Two Two ℤ
A = matrix2x2 (1 , 2) (3 , 4)
B = matrix2x2 (5 , 6) (7 , 8)

-- Matrix multiplication, addition, literals.
_ : A * B ≡ matrix2x2 (19 , 22) (43 , 50)
_ = refl
_ : A + 1 ≡ matrix2x2 (2 , 2) (3 , 5)
_ = refl
_ : A - A ≡ 0
_ = refl
_ : (Matrix Two Two ℤ ∋ 3) ≡ matrix2x2 (3 , 0) (0 , 3)
_ = refl
_ : - A ≡ matrix2x2 (-1 , -2) (-3 , -4)
_ = refl
_ : tr A ≡ 5
_ = refl
_ : from-matrix2x2 (matrix-transpose A) ≡ ((1 , 3) , (2 , 4))
_ = refl

-- Non-square matrices.
C : Matrix Two Three ℤ
C = Matrix' ((1 ∷ 4 ∷ []) ∷ (2 ∷ 5 ∷ []) ∷ (3 ∷ 6 ∷ []) ∷ [])

_ : rows-of-matrix C ≡ (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []
_ = refl
_ : columns-of-matrix (C ·*· column3 (1 , 0 , -1)) ≡ (-2 ∷ -2 ∷ []) ∷ []
_ = refl
_ : matrix-of-rows ((1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []) ≡ just C
_ = refl
_ : matrix {Two} {Three} {ℤ} ((1 ∷ 2 ∷ []) ∷ []) ≡ nothing
_ = refl
_ : matrix-index C 1 2 ≡ just 6
_ = refl
_ : matrix-index C 2 0 ≡ nothing
_ = refl
_ : matrix-size C ≡ (2 , 3)
_ = refl
_ : hs-sqnorm C ≡ 91
_ = refl
_ : matrix-entries C ≡ 1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ 6 ∷ []
_ = refl

-- Block matrices.
_ : tensor A B ≡ matrix4x4 (5 , 6 , 10 , 12) (7 , 8 , 14 , 16) (15 , 18 , 20 , 24) (21 , 24 , 28 , 32)
_ = refl
_ : oplus A B ≡ matrix4x4 (1 , 2 , 0 , 0) (3 , 4 , 0 , 0) (0 , 0 , 5 , 6) (0 , 0 , 7 , 8)
_ = refl
_ : (Matrix Four Four ℤ ∋ swap * swap) ≡ 1
_ = refl
_ : matrix-controlled (matrix2x2 (0 , 1) (1 , 0)) ≡ (Matrix Four Four ℤ ∋ cnot)
_ = refl

-- Vectors.
_ : vector {Three} (1 ∷ 2 ∷ 3 ∷ []) ≡ just (Vector Three ℤ ∋ (1 ∷ 2 ∷ 3 ∷ []))
_ = refl
_ : vector-transpose ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ (5 ∷ 6 ∷ []) ∷ []) ≡ (Vector Two (Vector Three ℤ) ∋ ((1 ∷ 3 ∷ 5 ∷ []) ∷ (2 ∷ 4 ∷ 6 ∷ []) ∷ []))
_ = refl
_ : (Vector Four ℕ ∋ vector-enum) ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
_ = refl
_ : fromNNat (nnat {Ten-and Eight}) ≡ 18
_ = refl

-- The ring of matrices over 𝔻[ω]: H² = 1, T⁸ = 1, ω-phases.
Hd Td : U2 DOmega
Hd = roothalf * matrix2x2 (1 , 1) (1 , -1)
Td = matrix2x2 (1 , 0) (0 , ω)

_ : Hd * Hd ≡ 1
_ = refl
_ : Td ^ 4 * Td ^ 4 ≡ 1
_ = refl
_ : Td ^ 4 ≡ matrix2x2 (1 , 0) (0 , -1)
_ = refl
_ : (U2 DOmega ∋ ω) ^ 4 ≡ -1
_ = refl
_ : adj Td * Td ≡ 1
_ = refl
_ : denomexp Hd ≡ 1
_ = refl
_ : maybe-dyadic (U2 QOmega ∋ half * 1) ≡ just (U2 DOmega ∋ half * 1)
_ = refl

-- Printing.
_ : show A ≡ "matrix [[1,2],[3,4]]"
_ = refl
_ : show (Matrix Two Two ℤ ∋ matrix2x2 (1 , 2) (3 , -4)) ≡ "matrix [[1,2],[3,-4]]"
_ = refl
_ : show (Vector Three ℤ ∋ (1 ∷ 2 ∷ 3 ∷ [])) ≡ "vector [1,2,3]"
_ = refl
_ : show Hd ≡ "roothalf * matrix [[Omega 0 0 0 1,Omega 0 0 0 1],[Omega 0 0 0 1,Omega 0 0 0 (-1)]]"
_ = refl
_ : show (U2 DRootTwo ∋ matrix2x2 (roothalf , 1) (0 , roottwo)) ≡ "roothalf * matrix [[1,roottwo],[0,2]]"
_ = refl
_ : show (U2 DRComplex ∋ matrix2x2 (i , 1) (0 , roottwo)) ≡ "matrix [[i,1],[0,roottwo]]"
_ = refl
_ : show (U2 QRootTwo ∋ matrix2x2 (roothalf , 1) (0 , roottwo)) ≡ "matrix [[1/2*roottwo,1],[0,roottwo]]"
_ = refl
