{-# OPTIONS --safe --without-K #-}

-- Modulo gamma squared only the relative 1/i phase of a row pair matters.
module GauInt.Matrix.RelativePhase where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra using (*-assoc; *-identityˡ; unit-conjugate; Unit; unit-product; unit-unscale)
open import GauInt.Matrix using (Mat)
open import GauInt.Gamma.Congruence
open import GauInt.Units using (phaseToZI; unit-phase)
open import Finite.Check
open import Finite.Enumeration using (decExists)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst; subst₂)

-- The phases 1 and i, indexed by a bit.
bitPhase : Fin 2 → Fin 4
bitPhase 0F = 0F
bitPhase 1F = 1F

abstract
  phase-bit : ∀ p → Σ[ b ∈ Fin 2 ] Cong 2 (phaseToZI p) (phaseToZI (bitPhase b))
  phase-bit = checkFin 4 _ (λ p → decExists 2 _ (λ b → cong? 2 (phaseToZI p) (phaseToZI (bitPhase b)))) tt

unit-bit : ∀ u → Unit u → Σ[ b ∈ Fin 2 ] Cong 2 u (phaseToZI (bitPhase b))
unit-bit u hu = finish (unit-phase u hu)
  where
  finish : (Σ[ p ∈ Fin 4 ] u ≡ phaseToZI p) → Σ[ b ∈ Fin 2 ] Cong 2 u (phaseToZI (bitPhase b))
  finish (p , hp) = subst (λ v → Σ[ b ∈ Fin 2 ] Cong 2 v (phaseToZI (bitPhase b))) (sym hp) (phase-bit p)

relative-pair : ∀ u v → Unit u → Unit v →
  Σ[ b ∈ Fin 2 ] (∀ x y → Cong 2 (u * x) (v * y) → Cong 2 x (phaseToZI (bitPhase b) * y))
relative-pair u v hu hv = finish (unit-bit (TC.adj u * v) (unit-product (TC.adj u) v (unit-conjugate u hu) hv))
  where
  finish : (Σ[ b ∈ Fin 2 ] Cong 2 (TC.adj u * v) (phaseToZI (bitPhase b))) →
    Σ[ b ∈ Fin 2 ] (∀ x y → Cong 2 (u * x) (v * y) → Cong 2 x (phaseToZI (bitPhase b) * y))
  finish (b , hb) = b , λ x y h → cong-trans 2 x ((TC.adj u * v) * y) (phaseToZI (bitPhase b) * y)
    (subst₂ (Cong 2) (unit-unscale u x hu) (sym (*-assoc (TC.adj u) v y))
      (cong-mul 2 (TC.adj u) (TC.adj u) (u * x) (v * y) (cong-refl 2 (TC.adj u)) h))
    (cong-mul 2 (TC.adj u * v) (phaseToZI (bitPhase b)) y y hb (cong-refl 2 y))

RowCompatible : ∀ {n} → Mat n → Fin n → Fin n → Set
RowCompatible M i j = Σ[ u ∈ ZComplex ] Σ[ v ∈ ZComplex ]
  Data.Product._×_ (Unit u) (Data.Product._×_ (Unit v) (∀ k → Cong 2 (u * M i k) (v * M j k)))

row-compatible-sym : ∀ {n} (M : Mat n) i j → RowCompatible M i j → RowCompatible M j i
row-compatible-sym M i j (u , v , hu , hv , h) = v , u , hv , hu , λ k → cong-sym 2 (u * M i k) (v * M j k) (h k)

row-relative : ∀ {n} (M : Mat n) i j → RowCompatible M i j → Σ[ b ∈ Fin 2 ] (∀ k → Cong 2 (M i k) (phaseToZI (bitPhase b) * M j k))
row-relative M i j (u , v , hu , hv , h) = finish (relative-pair u v hu hv)
  where
  finish : (Σ[ b ∈ Fin 2 ] (∀ x y → Cong 2 (u * x) (v * y) → Cong 2 x (phaseToZI (bitPhase b) * y))) →
    Σ[ b ∈ Fin 2 ] (∀ k → Cong 2 (M i k) (phaseToZI (bitPhase b) * M j k))
  finish (b , hb) = b , λ k → hb (M i k) (M j k) (h k)
