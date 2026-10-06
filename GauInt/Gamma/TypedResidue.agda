{-# OPTIONS --safe --without-K #-}

-- Once parity is fixed, one Boolean selects every residue modulo γ².
module GauInt.Gamma.TypedResidue where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Gamma using (γ; powγ)
open import GauInt.Matrix using (Mat)
open import GauInt.Gamma.Bit using (bit; congruent-same-bit)
import GauInt.Gamma.Congruence as G
import GauInt.Matrix.Congruence as MG
import GauInt.Gamma.Residue as R
open import Finite.Check
open import Data.Bool using (Bool; false; true)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

representative : Bool → Bool → ZComplex
representative false false = 0#
representative false true = γ
representative true false = 1#
representative true true = TC.i

refinement : R.Code → Bool
refinement 0F = false
refinement 1F = false
refinement 2F = true
refinement 3F = true
refinement 4F = false
refinement 5F = false
refinement 6F = true
refinement 7F = true

abstract
  representative-check : ∀ c → G.Cong 2 (R.decode c)
    (representative (bit (R.decode c)) (refinement c))
  representative-check = checkFin 8 _ (λ c → G.cong? 2 (R.decode c)
    (representative (bit (R.decode c)) (refinement c))) tt

residueBit : ZComplex → Bool
residueBit z = refinement (R.encode z)

representative-spec : ∀ z → G.Cong 2 z (representative (bit z) (residueBit z))
representative-spec z = subst (λ b → G.Cong 2 z (representative b (residueBit z)))
  (sym (congruent-same-bit z (R.decode (R.encode z))
    (G.lower 1 z (R.decode (R.encode z)) h)))
  (G.cong-trans 2 z (R.decode (R.encode z))
    (representative (bit (R.decode (R.encode z))) (residueBit z)) h (representative-check (R.encode z)))
  where
  h = G.lower 2 z (R.decode (R.encode z)) (R.encode-spec z)

typed : ∀ {n} → (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool) → Mat n
typed shape digits i j = representative (shape i j) (digits i j)

typed-coverage : ∀ {n} (M : Mat n) shape → (∀ i j → bit (M i j) ≡ shape i j) →
  Σ[ digits ∈ (Fin n → Fin n → Bool) ] MG.Matrices 2 M (typed shape digits)
typed-coverage M shape h = (λ i j → residueBit (M i j)) , λ i j →
  subst (λ b → G.Cong 2 (M i j) (representative b (residueBit (M i j)))) (h i j)
    (representative-spec (M i j))
