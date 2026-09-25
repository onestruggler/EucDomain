-- Checks of Kopt.Gates (the gate set 𝒢 and the semantics ⟦_⟧)
-- against Section I of the paper. All checks in this module are by
-- refl, i.e. they are performed by the type checker.
--
-- Equalities of 4×4 matrices are stated as boolean tests "m == m'"
-- (using the decidable equality of 𝔻[i]) rather than as propositional
-- equalities: for circuits of more than a few gates the conversion
-- checker needs gigabytes of heap on such a goal, whereas evaluating
-- the boolean is cheap.

{-# OPTIONS --without-K --safe #-}

module Test.KoptGates where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Bool.ListAction using (all ; and)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates

-- The gate set, in the order of the paper's Definition I.1, plus the
-- scalar gate and the two controlled-K gates.
all-gates : List Gate
all-gates = X₀ ∷ X₁ ∷ Z₀ ∷ Z₁ ∷ S₀ ∷ S₁ ∷ K₀ ∷ K₁ ∷ CZ ∷ CS ∷ CX ∷ XC ∷ Ex ∷ Ii ∷ CK ∷ KC ∷ []

-- ----------------------------------------------------------------------
-- * Every gate is unitary

unitary? : Gate -> Bool
unitary? g = ((⟦ g ⟧g * adjoint ⟦ g ⟧g) == 1) ∧ ((adjoint ⟦ g ⟧g * ⟦ g ⟧g) == 1)

_ : all unitary? all-gates ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * Gate inverses

inverts? : Gate -> Bool
inverts? g = ((⟦ inv-gate g ⟧ * ⟦ g ⟧g) == 1) ∧ ((⟦ g ⟧g * ⟦ inv-gate g ⟧) == 1)

_ : all inverts? all-gates ≡ true
_ = refl

-- inv-circuit inverts circuits (⟦inv-circuit c⟧·⟦c⟧ = 1 and
-- ⟦c⟧·⟦inv-circuit c⟧ = 1), for a selection of circuits.
sample-circuits : List Circuit
sample-circuits =
    []
  ∷ (K₁ ∷ CS ∷ K₁ ∷ [])
  ∷ (CZ ∷ Z₀ ∷ S₀ ∷ Z₁ ∷ S₁ ∷ K₁ ∷ CS ∷ K₁ ∷ S₁ ∷ Ii ∷ [])
  ∷ (K₀ ∷ K₁ ∷ CZ ∷ K₀ ∷ K₁ ∷ CZ ∷ [])
  ∷ (Ex ∷ CX ∷ XC ∷ CX ∷ Ex ∷ [])
  ∷ (S₀ ∷ S₁ ∷ CS ∷ Ii ∷ X₀ ∷ X₁ ∷ Z₀ ∷ Z₁ ∷ [])
  ∷ (CK ∷ KC ∷ CK ∷ [])
  ∷ (K₁ ∷ K₀ ∷ CS ∷ K₁ ∷ K₀ ∷ CS ∷ K₁ ∷ K₀ ∷ [])
  ∷ []

inverts-circuit? : Circuit -> Bool
inverts-circuit? c = ((⟦ inv-circuit c ⟧ * ⟦ c ⟧) == 1) ∧ ((⟦ c ⟧ * ⟦ inv-circuit c ⟧) == 1)

_ : all inverts-circuit? sample-circuits ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * The derived gates of Section I

derived-gate-identities : List Bool
derived-gate-identities =
  -- X = KZK·i
    (⟦ X₀ ⟧g == ⟦ K₀ ∷ Z₀ ∷ K₀ ∷ Ii ∷ [] ⟧)
  ∷ (⟦ X₁ ⟧g == ⟦ K₁ ∷ Z₁ ∷ K₁ ∷ Ii ∷ [] ⟧)
  -- Z = S²
  ∷ (⟦ Z₀ ⟧g == ⟦ S₀ ∷ S₀ ∷ [] ⟧)
  ∷ (⟦ Z₁ ⟧g == ⟦ S₁ ∷ S₁ ∷ [] ⟧)
  -- CZ = CS²
  ∷ (⟦ CZ ⟧g == ⟦ CS ∷ CS ∷ [] ⟧)
  -- CX = K₁CZK₁·i, and the mirror image XC = K₀CZK₀·i
  ∷ (⟦ CX ⟧g == ⟦ K₁ ∷ CZ ∷ K₁ ∷ Ii ∷ [] ⟧)
  ∷ (⟦ XC ⟧g == ⟦ K₀ ∷ CZ ∷ K₀ ∷ Ii ∷ [] ⟧)
  -- XC = Ex·CX·Ex and Ex = CX·XC·CX
  ∷ (⟦ XC ⟧g == ⟦ Ex ∷ CX ∷ Ex ∷ [] ⟧)
  ∷ (⟦ Ex ⟧g == ⟦ CX ∷ XC ∷ CX ∷ [] ⟧)
  -- CK = I ⊕ K and KC = Ex·CK·Ex
  ∷ (⟦ CK ⟧g == oplus id-matrix k-matrix)
  ∷ (⟦ KC ⟧g == ⟦ Ex ∷ CK ∷ Ex ∷ [] ⟧)
  -- Equation (1): CK = CZ·Z₀S₀Z₁S₁K₁CSK₁S₁·i, and its mirror image
  ∷ (⟦ CK ⟧g == ⟦ ck-expansion ⟧)
  ∷ (⟦ KC ⟧g == ⟦ kc-expansion ⟧)
  -- desugar-ck preserves the semantics
  ∷ (⟦ desugar-ck (CK ∷ K₀ ∷ KC ∷ []) ⟧ == ⟦ CK ∷ K₀ ∷ KC ∷ [] ⟧)
  ∷ []

_ : and derived-gate-identities ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * Gate counts (Definition V.1)

_ : kc (CK ∷ K₀ ∷ K₁ ∷ CS ∷ Ex ∷ []) ≡ 2
_ = refl
_ : csc (CK ∷ K₀ ∷ K₁ ∷ CS ∷ Ex ∷ []) ≡ 1
_ = refl
_ : rlen (CK ∷ K₀ ∷ K₁ ∷ CS ∷ Ex ∷ []) ≡ 5
_ = refl
_ : kc (desugar-ck (CK ∷ [])) ≡ 2
_ = refl
_ : csc (desugar-ck (CK ∷ [])) ≡ 1
_ = refl
_ : rlen (desugar-ck (CK ∷ [])) ≡ 10
_ = refl

-- ----------------------------------------------------------------------
-- * Printing

_ : show (K₁ ∷ CS ∷ K₁ ∷ Ii ∷ []) ≡ "[K1,CS,K1,II]"
_ = refl
_ : show X₀ ≡ "X0"
_ = refl

-- ----------------------------------------------------------------------
-- * The lde of the gates (Definition II.1)

-- K is the only gate of 𝒢 whose matrix is not integral (Remark
-- II.10): it has lde 1, and so do the controlled-K gates; every other
-- gate has lde 0.
_ : map (λ g -> lde ⟦ g ⟧g) all-gates
      ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ []
_ = refl

-- ----------------------------------------------------------------------
-- * Remark II.2: the lde of a two-qubit Clifford operator is ≤ 2

clifford-circuits : List Circuit
clifford-circuits =
    (K₀ ∷ [])
  ∷ (K₀ ∷ K₁ ∷ [])
  ∷ (K₀ ∷ CZ ∷ K₀ ∷ [])
  ∷ (K₀ ∷ K₁ ∷ CZ ∷ K₀ ∷ K₁ ∷ [])
  ∷ (K₀ ∷ S₀ ∷ K₀ ∷ K₁ ∷ S₁ ∷ K₁ ∷ CZ ∷ [])
  ∷ (Ex ∷ K₀ ∷ CZ ∷ K₁ ∷ Ex ∷ K₀ ∷ [])
  ∷ []

_ : all (λ c -> lde ⟦ c ⟧ ≤ᵇ 2) clifford-circuits ≡ true
_ = refl

-- The (1,l)-residue of K₀K₁ is the all-odd matrix, i.e. pattern (vi)
-- of Lemma IV.1.
_ : (residue1-lde ⟦ K₀ ∷ K₁ ∷ [] ⟧ == matrix4x4 (Odd , Odd , Odd , Odd)
                                                (Odd , Odd , Odd , Odd)
                                                (Odd , Odd , Odd , Odd)
                                                (Odd , Odd , Odd , Odd)) ≡ true
_ = refl
