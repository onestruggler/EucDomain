{-# OPTIONS --safe --without-K #-}

-- Unit normal forms modulo gamma cubed: every residue is a unit multiple of
-- one of four representatives, and the unit preserves the norm residue.
module GauInt.Gamma.UnitNormal where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Gamma using (Oddγ) renaming (gaussianParity to parity)
open import GauInt.Gamma.Residue using (Code; decode; encode; encode-spec)
open import GauInt.Units using (phaseToZI)
open import Finite.Check using (checkFin; decImplies)
import GauInt.Parity as GP
import GauInt.Gamma.Congruence as G
open import Data.Fin using (Fin; _≟_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F)
import Data.Nat as N
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

-- The four unit-orbit representatives 0, 1, 1 + i and 2i.
representative : Fin 4 → Code
representative 0F = 0F
representative 1F = 1F
representative 2F = 2F
representative 3F = 4F

canonicalIndex : Code → Fin 4
canonicalIndex 0F = 0F
canonicalIndex 1F = 1F
canonicalIndex 2F = 2F
canonicalIndex 3F = 1F
canonicalIndex 4F = 3F
canonicalIndex 5F = 1F
canonicalIndex 6F = 2F
canonicalIndex 7F = 1F

phaseCode : Code → Fin 4
phaseCode 0F = 0F
phaseCode 1F = 0F
phaseCode 2F = 0F
phaseCode 3F = 1F
phaseCode 4F = 0F
phaseCode 5F = 2F
phaseCode 6F = 1F
phaseCode 7F = 3F

canonicalValue : ZComplex → ZComplex
canonicalValue z = decode (representative (canonicalIndex (encode z)))

abstract
  phase-spec : ∀ c → G.Cong 3 (phaseToZI (phaseCode c) * decode c)
    (decode (representative (canonicalIndex c)))
  phase-spec = checkFin 8 _ (λ c → G.cong? 3 (phaseToZI (phaseCode c) * decode c)
    (decode (representative (canonicalIndex c)))) tt

  norm-spec : ∀ c → G.Cong 3 (decode c * TC.adj (decode c))
    (decode (representative (canonicalIndex c)) * TC.adj (decode (representative (canonicalIndex c))))
  norm-spec = checkFin 8 _ (λ c → G.cong? 3 (decode c * TC.adj (decode c))
    (decode (representative (canonicalIndex c)) * TC.adj (decode (representative (canonicalIndex c))))) tt

  odd-spec : ∀ c → parity (decode c) ≡ 1 → canonicalIndex c ≡ 1F
  odd-spec = checkFin 8 _ (λ c → decImplies (parity (decode c) N.≟ 1) (canonicalIndex c ≟ 1F)) tt

canonical-phase : ∀ z → G.Cong 3 (phaseToZI (phaseCode (encode z)) * z) (canonicalValue z)
canonical-phase z = G.cong-trans 3 (u * z) (u * decode (encode z)) (canonicalValue z)
  (G.cong-mul 3 u u z (decode (encode z)) (G.cong-refl 3 u) (encode-spec z)) (phase-spec (encode z))
  where u = phaseToZI (phaseCode (encode z))

canonical-norm : ∀ z → G.Cong 3 (z * TC.adj z) (canonicalValue z * TC.adj (canonicalValue z))
canonical-norm z = G.cong-trans 3 (z * TC.adj z) (decode (encode z) * TC.adj (decode (encode z)))
  (canonicalValue z * TC.adj (canonicalValue z))
  (G.cong-mul 3 z (decode (encode z)) (TC.adj z) (TC.adj (decode (encode z)))
    (encode-spec z) (G.cong-conj 3 z (decode (encode z)) (encode-spec z))) (norm-spec (encode z))

canonical-odd : ∀ z → Oddγ z → canonicalIndex (encode z) ≡ 1F
canonical-odd z h with GP.parity-cases z
... | inj₁ he = ⊥-elim (h (GP.zero-parity-even z he))
... | inj₂ ho = odd-spec (encode z)
  (trans (sym (G.parity-congruent 2 z (decode (encode z)) (encode-spec z))) ho)
