-- The residues of the diagonal unitaries, as closed data.
--
-- The refinements of Section IV B multiply the residue matrix by
-- im-res e, the ρ₂-residue of the diagonal unitary diag(i^e₀,…,i^e₃), and
-- by the residues of one or two gates. im-res is defined through 𝔻[i]:
-- it takes the diagonal matrix, then its whole part, then ρ₂ of each
-- entry. Any enumeration that runs a refinement must therefore not have
-- im-res inside it, or the type checker evaluates sixteen entries of
-- dyadic arithmetic per candidate.
--
-- So the sixteen values that can occur are tabulated here as pure ℤ[i]/γ²
-- data and matched against im-res once each. The exponents that occur are
-- 0 and 1, because they are produced by im-exp, which is a test; that is
-- im-exp-bit below.

{-# OPTIONS --without-K --safe #-}

module Kopt.ImRes where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Permutations using (Tuple4)
open import Kopt.Gates using (Gate ; CX ; Ex ; Circuit)
open import Kopt.Patterns using (R2 ; r2-zero ; r2-one ; r2-i ; im-exp ; im-res ; r2-of-circuit)
open import Kopt.Descent using (_∈ˡ_ ; here ; there)

-- ----------------------------------------------------------------------
-- * The exponents that occur

-- im-exp is a test, so it is 0 or 1.
im-exp-bit : (v : R2) -> (im-exp v ≡ 0) ⊎ (im-exp v ≡ 1)
im-exp-bit (Even ∷ Even ∷ []) = inj₁ refl
im-exp-bit (Even ∷ Odd ∷ []) = inj₁ refl
im-exp-bit (Odd ∷ Even ∷ []) = inj₁ refl
im-exp-bit (Odd ∷ Odd ∷ []) = inj₂ refl

-- The sixteen exponent vectors over {0,1}.
bits4 : List Tuple4
bits4 =
    (0 , 0 , 0 , 0) ∷ (1 , 0 , 0 , 0) ∷ (0 , 1 , 0 , 0) ∷ (1 , 1 , 0 , 0)
  ∷ (0 , 0 , 1 , 0) ∷ (1 , 0 , 1 , 0) ∷ (0 , 1 , 1 , 0) ∷ (1 , 1 , 1 , 0)
  ∷ (0 , 0 , 0 , 1) ∷ (1 , 0 , 0 , 1) ∷ (0 , 1 , 0 , 1) ∷ (1 , 1 , 0 , 1)
  ∷ (0 , 0 , 1 , 1) ∷ (1 , 0 , 1 , 1) ∷ (0 , 1 , 1 , 1) ∷ (1 , 1 , 1 , 1)
  ∷ []

-- ----------------------------------------------------------------------
-- * The table

-- ρ₂(i^e) for e = 0 and e = 1.
ime : ℕ -> R2
ime 0 = r2-one
ime _ = r2-i

-- The diagonal R2 matrix. This is pure ℤ[i]/γ² data: no 𝔻[i] anywhere.
imr : Tuple4 -> Matrix 4 4 R2
imr (a , b , c , d) =
  Matrix' ( (ime a ∷ r2-zero ∷ r2-zero ∷ r2-zero ∷ [])
          ∷ (r2-zero ∷ ime b ∷ r2-zero ∷ r2-zero ∷ [])
          ∷ (r2-zero ∷ r2-zero ∷ ime c ∷ r2-zero ∷ [])
          ∷ (r2-zero ∷ r2-zero ∷ r2-zero ∷ ime d ∷ []) ∷ [])

-- It agrees with im-res on every exponent vector that can occur. Sixteen
-- closed checks, which is where the dyadic arithmetic is paid for -- once
-- each, instead of once per candidate inside an enumeration.
imr-ok : (e : Tuple4) -> e ∈ˡ bits4 -> imr e ≡ im-res e
imr-ok _ here = refl
imr-ok _ (there here) = refl
imr-ok _ (there (there here)) = refl
imr-ok _ (there (there (there here))) = refl
imr-ok _ (there (there (there (there here)))) = refl
imr-ok _ (there (there (there (there (there here))))) = refl
imr-ok _ (there (there (there (there (there (there here)))))) = refl
imr-ok _ (there (there (there (there (there (there (there here))))))) = refl
imr-ok _ (there (there (there (there (there (there (there (there here)))))))) = refl
imr-ok _ (there (there (there (there (there (there (there (there (there here))))))))) = refl
imr-ok _ (there (there (there (there (there (there (there (there (there (there here)))))))))) =
  refl
imr-ok _ (there (there (there (there (there (there (there (there (there (there
  (there here))))))))))) = refl
imr-ok _ (there (there (there (there (there (there (there (there (there (there
  (there (there here)))))))))))) = refl
imr-ok _ (there (there (there (there (there (there (there (there (there (there
  (there (there (there here))))))))))))) = refl
imr-ok _ (there (there (there (there (there (there (there (there (there (there
  (there (there (there (there here)))))))))))))) = refl
imr-ok _ (there (there (there (there (there (there (there (there (there (there
  (there (there (there (there (there here))))))))))))))) = refl

-- Every exponent vector built by im-exp is in the list. The four values
-- are generalised first: matching refl against `im-exp v ≡ 0` is stuck,
-- since im-exp v does not reduce for a variable v, while matching it
-- against `a ≡ 0` for a variable a substitutes a := 0.
∈-bits4 : (v₀ v₁ v₂ v₃ : R2) ->
          (im-exp v₀ , im-exp v₁ , im-exp v₂ , im-exp v₃) ∈ˡ bits4
∈-bits4 v₀ v₁ v₂ v₃ =
  go (im-exp v₀) (im-exp v₁) (im-exp v₂) (im-exp v₃)
     (im-exp-bit v₀) (im-exp-bit v₁) (im-exp-bit v₂) (im-exp-bit v₃)
  where
    go : (a b c d : ℕ) -> (a ≡ 0) ⊎ (a ≡ 1) -> (b ≡ 0) ⊎ (b ≡ 1) ->
         (c ≡ 0) ⊎ (c ≡ 1) -> (d ≡ 0) ⊎ (d ≡ 1) -> (a , b , c , d) ∈ˡ bits4
    go _ _ _ _ (inj₁ refl) (inj₁ refl) (inj₁ refl) (inj₁ refl) =
      here
    go _ _ _ _ (inj₂ refl) (inj₁ refl) (inj₁ refl) (inj₁ refl) =
      (there here)
    go _ _ _ _ (inj₁ refl) (inj₂ refl) (inj₁ refl) (inj₁ refl) =
      (there (there here))
    go _ _ _ _ (inj₂ refl) (inj₂ refl) (inj₁ refl) (inj₁ refl) =
      (there (there (there here)))
    go _ _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ refl) (inj₁ refl) =
      (there (there (there (there here))))
    go _ _ _ _ (inj₂ refl) (inj₁ refl) (inj₂ refl) (inj₁ refl) =
      (there (there (there (there (there here)))))
    go _ _ _ _ (inj₁ refl) (inj₂ refl) (inj₂ refl) (inj₁ refl) =
      (there (there (there (there (there (there here))))))
    go _ _ _ _ (inj₂ refl) (inj₂ refl) (inj₂ refl) (inj₁ refl) =
      (there (there (there (there (there (there (there here)))))))
    go _ _ _ _ (inj₁ refl) (inj₁ refl) (inj₁ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there here))))))))
    go _ _ _ _ (inj₂ refl) (inj₁ refl) (inj₁ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there (there here)))))))))
    go _ _ _ _ (inj₁ refl) (inj₂ refl) (inj₁ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there (there (there here))))))))))
    go _ _ _ _ (inj₂ refl) (inj₂ refl) (inj₁ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there (there (there (there here)))))))))))
    go _ _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))
    go _ _ _ _ (inj₂ refl) (inj₁ refl) (inj₂ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))
    go _ _ _ _ (inj₁ refl) (inj₂ refl) (inj₂ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))
    go _ _ _ _ (inj₂ refl) (inj₂ refl) (inj₂ refl) (inj₂ refl) =
      (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))

-- ----------------------------------------------------------------------
-- * The residues of the circuits that the refinements use
--
-- Besides the diagonal unitaries, the refinements multiply by the residue
-- of a one- or two-gate circuit: CX, Ex, or CX followed by Ex. Those go
-- through 𝔻[i] too, so they are tabulated here as well. All three are
-- permutation matrices, so the residues are the same patterns with r2-one
-- for 1 and r2-zero for 0.

private
  o : R2
  o = r2-one
  z : R2
  z = r2-zero

-- The identity, which is the residue of the empty circuit.
r2-nil : Matrix 4 4 R2
r2-nil = Matrix' ((o ∷ z ∷ z ∷ z ∷ []) ∷ (z ∷ o ∷ z ∷ z ∷ [])
                ∷ (z ∷ z ∷ o ∷ z ∷ []) ∷ (z ∷ z ∷ z ∷ o ∷ []) ∷ [])

-- cnot: it fixes e₀ and e₁ and exchanges e₂ and e₃.
r2-cx : Matrix 4 4 R2
r2-cx = Matrix' ((o ∷ z ∷ z ∷ z ∷ []) ∷ (z ∷ o ∷ z ∷ z ∷ [])
               ∷ (z ∷ z ∷ z ∷ o ∷ []) ∷ (z ∷ z ∷ o ∷ z ∷ []) ∷ [])

-- swap: it fixes e₀ and e₃ and exchanges e₁ and e₂.
r2-ex : Matrix 4 4 R2
r2-ex = Matrix' ((o ∷ z ∷ z ∷ z ∷ []) ∷ (z ∷ z ∷ o ∷ z ∷ [])
               ∷ (z ∷ o ∷ z ∷ z ∷ []) ∷ (z ∷ z ∷ z ∷ o ∷ []) ∷ [])

-- cnot after swap.
r2-cxex : Matrix 4 4 R2
r2-cxex = Matrix' ((o ∷ z ∷ z ∷ z ∷ []) ∷ (z ∷ z ∷ z ∷ o ∷ [])
                 ∷ (z ∷ o ∷ z ∷ z ∷ []) ∷ (z ∷ z ∷ o ∷ z ∷ []) ∷ [])

r2-nil-ok : r2-of-circuit [] ≡ r2-nil
r2-nil-ok = refl

r2-cx-ok : r2-of-circuit (CX ∷ []) ≡ r2-cx
r2-cx-ok = refl

r2-ex-ok : r2-of-circuit (Ex ∷ []) ≡ r2-ex
r2-ex-ok = refl

r2-cxex-ok : r2-of-circuit (CX ∷ Ex ∷ []) ≡ r2-cxex
r2-cxex-ok = refl
