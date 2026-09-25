{-# OPTIONS --without-K --safe #-}
module Kopt.SPHalf where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Descent
open import Kopt.Optimality using (==⇒≡)

-- The two ten-gate products of Equation (1) are too big for a single
-- conversion check: a product of more than about five 4×4 matrices
-- over 𝔻[i] exhausts a 3 GB heap (this is what made this module
-- uncheckable). Both expansions are therefore split at their first K
-- gate. The K-free prefix CZ·Z₀S₀Z₁S₁ (resp. CZ·Z₁S₁Z₀S₀) is the
-- diagonal generalized permutation diag(1,-i,-i,1); naming it turns
-- one ten-fold product into two independent five-fold ones, each of
-- which the type checker handles in seconds.
private
  ck-pre ck-post kc-pre kc-post : Circuit
  ck-pre = CZ ∷ Z₀ ∷ S₀ ∷ Z₁ ∷ S₁ ∷ []
  ck-post = K₁ ∷ CS ∷ K₁ ∷ S₁ ∷ Ii ∷ []
  kc-pre = CZ ∷ Z₁ ∷ S₁ ∷ Z₀ ∷ S₀ ∷ []
  kc-post = K₀ ∷ CS ∷ K₀ ∷ S₀ ∷ Ii ∷ []

  -- diag(1, -i, -i, 1)
  pre-gp : GP
  pre-gp = gperm id4p (ph0 , ph3 , ph3 , ph0) refl

  ck-pre-ok : ⟦ ck-pre ⟧ ≡ gp-mat pre-gp
  ck-pre-ok = ==⇒≡ refl

  kc-pre-ok : ⟦ kc-pre ⟧ ≡ gp-mat pre-gp
  kc-pre-ok = ==⇒≡ refl

  -- Note: these two are propositional equalities proved by refl, not
  -- boolean tests proved by "==⇒≡ refl". For these products -- which
  -- contain K gates, so the entries are dyadic fractions and not just
  -- powers of i -- the boolean test is the expensive one: evaluating
  -- m == m' makes the decidable equality build the equality *proof* of
  -- two 4×4 matrices over 𝔻[i], which exhausts a 3 GB heap, whereas
  -- comparing the two computed matrices directly costs seconds.
  ck-post-ok : gp-mat pre-gp * ⟦ ck-post ⟧ ≡ ⟦ CK ⟧g
  ck-post-ok = refl

  kc-post-ok : gp-mat pre-gp * ⟦ kc-post ⟧ ≡ ⟦ KC ⟧g
  kc-post-ok = refl

  ck-ok : ⟦ ck-expansion ⟧ ≡ ⟦ CK ⟧g
  ck-ok = trans (trans (⟦⟧-++ ck-pre ck-post)
                       (cong (λ m -> m * ⟦ ck-post ⟧) ck-pre-ok))
                ck-post-ok

  kc-ok : ⟦ kc-expansion ⟧ ≡ ⟦ KC ⟧g
  kc-ok = trans (trans (⟦⟧-++ kc-pre kc-post)
                       (cong (λ m -> m * ⟦ kc-post ⟧) kc-pre-ok))
                kc-post-ok

