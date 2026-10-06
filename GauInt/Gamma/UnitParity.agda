{-# OPTIONS --safe --without-K #-}

-- Unit phases preserve the parity of integer entries whenever both sides
-- are real. This handles the row phases in Clifford spin matrices.
module GauInt.Gamma.UnitParity where
open import GauInt.Gamma.Integer using (zero-parity-even; halfReal; even-integer-double)

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra using (lift; Unit)
open import Integer.Parity
open import Integer.Congruence
open import Integer.Residues using (multiple2-natural)
open import GauInt.Gamma using (Evenγ; even-mul; even-unscale)
open import Data.Integer using (+_)
import Data.Integer as Z
import Data.Integer.Properties as ZP
open import Data.Nat using (_%_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

even-integer-parity : ∀ x → Evenγ (lift x) → parity x ≡ 0
even-integer-parity x he with parity-cases x
... | inj₁ h = h
... | inj₂ h = ⊥-elim (bad eq)
  where
  cx : Cong (+ 2) x (+ 0)
  cx = halfReal x , trans (even-integer-double x he) (sym (ZP.+-identityˡ ((+ 2) Z.* halfReal x)))
  cp : Cong (+ 2) (+ (parity x)) (+ 0)
  cp = cong-trans (+ 2) (+ (parity x)) x (+ 0) (cong-sym (+ 2) x (+ (parity x)) (parity-congruence x)) cx
  eq : 1 % 2 ≡ 0
  eq = trans (sym (cong (_% 2) h)) (multiple2-natural (parity x) cp)
  bad : 1 % 2 ≡ 0 → ⊥
  bad ()

unit-integer-parity : ∀ u x y → Unit u → lift x ≡ u * lift y → parity x ≡ parity y
unit-integer-parity u x y hu eq with parity-cases x | parity-cases y
... | inj₁ hx | inj₁ hy = trans hx (sym hy)
... | inj₂ hx | inj₂ hy = trans hx (sym hy)
... | inj₁ hx | inj₂ hy = ⊥-elim (bad (trans (sym hy) py))
  where
  py : parity y ≡ 0
  py = even-integer-parity y (even-unscale u (lift y) hu (subst Evenγ eq (zero-parity-even x hx)))
  bad : 1 ≡ 0 → ⊥
  bad ()
... | inj₂ hx | inj₁ hy = ⊥-elim (bad (trans (sym hx) px))
  where
  px : parity x ≡ 0
  px = even-integer-parity x (subst Evenγ (sym eq) (even-mul u (lift y) (zero-parity-even y hy)))
  bad : 1 ≡ 0 → ⊥
  bad ()
