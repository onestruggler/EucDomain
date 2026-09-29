-- Unitarity of a two-qubit operator, and the entries of U†U, UU† and
-- ρˡ₁(U), for
--
--   X. Bian and Y. Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis
--   of Two-Qubit Clifford+CS Operators" (2026).
--
-- Let U be a 4×4 unitary over 𝔻[i]. Unitarity is an explicit
-- hypothesis (U†·U = 1 and U·U† = 1), since the type Matrix 4 4
-- DComplex of the algorithm contains every matrix. This module reads
-- off the four consequences of unitarity that Section IV uses,
--
--   Σₖ Uₖⱼ·(Uₖⱼ)† = 1   for every column j,        (u-col)
--   Σₖ (Uⱼₖ)†·Uⱼₖ = 1   for every row j,           (u-row)
--   Σₖ Uₖⱼ·(Uₖⱼ')† = 0  for two distinct columns,  (o-col)
--   Σₖ (Uⱼₖ)†·Uⱼ'ₖ = 0  for two distinct rows,     (o-row)
--
-- together with the entries of the (1,l)-residue matrix ρˡ₁(U)
-- (residue1-matrix of Kopt.Base). Kopt.Unitary2 turns them into the
-- counting facts of Lemmas IV.2 and IV.3.
--
-- Performance: as recommended in the porting guide, everything outside
-- the module Entries is stated over 𝔻[i]- and ℤ[i]-VARIABLES only.
-- Entries is the one place where a matrix is taken apart: it reads the
-- entries of the three matrices off the sixteen entries of U.

{-# OPTIONS --without-K --safe #-}

module Kopt.Unitary where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; not ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; ∃ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Properties.Algebra

private
  module DR = IsCommutativeRing isCommutativeRing-DComplex
  module ZR = IsCommutativeRing isCommutativeRing-ZComplex
  module AD = IsInvolutiveRingEndo adj-DComplex

  Op : Set
  Op = Matrix 4 4 DComplex

-- ----------------------------------------------------------------------
-- * The lde of a 4-vector bounds the lde of its entries
--
-- lde (x ∷ y ∷ z ∷ w ∷ []) = max (lde x) (max (lde y) (max (lde z)
-- (max (lde w) 0))). These four lemmas are the ones of Kopt.Descent
-- (lde-4-0 … lde-4-3), repeated here so that this module does not
-- depend on Kopt.Descent.

module _ {T : Set} {{_ : LamDenomExp T}} (x y z w : T) where
  private
    M4 : ℕ
    M4 = lde (Vector 4 T ∋ (x ∷ y ∷ z ∷ w ∷ []))

  lde4-0 : lde x Nat.≤ M4
  lde4-0 = max-≤ˡ (lde x) _

  lde4-1 : lde y Nat.≤ M4
  lde4-1 = NatP.≤-trans (max-≤ˡ (lde y) _) (max-≤ʳ (lde x) _)

  lde4-2 : lde z Nat.≤ M4
  lde4-2 = NatP.≤-trans (NatP.≤-trans (max-≤ˡ (lde z) _) (max-≤ʳ (lde y) _)) (max-≤ʳ (lde x) _)

  lde4-3 : lde w Nat.≤ M4
  lde4-3 = NatP.≤-trans (NatP.≤-trans (NatP.≤-trans (max-≤ˡ (lde w) _) (max-≤ʳ (lde z) _))
                                      (max-≤ʳ (lde y) _))
                        (max-≤ʳ (lde x) _)

-- ----------------------------------------------------------------------
-- * Indices

-- The four coordinates. (Kopt.Descent has the same type, under the
-- name Pos; this module is independent of Kopt.Descent.)
data Ix : Set where
  ι0 ι1 ι2 ι3 : Ix

-- Are two indices different?
ix/= : Ix -> Ix -> Bool
ix/= ι0 ι0 = false
ix/= ι1 ι1 = false
ix/= ι2 ι2 = false
ix/= ι3 ι3 = false
ix/= _ _ = true

ix/=-sym : (r c : Ix) -> ix/= r c ≡ true -> ix/= c r ≡ true
ix/=-sym ι0 ι0 ()
ix/=-sym ι0 ι1 _ = refl
ix/=-sym ι0 ι2 _ = refl
ix/=-sym ι0 ι3 _ = refl
ix/=-sym ι1 ι0 _ = refl
ix/=-sym ι1 ι1 ()
ix/=-sym ι1 ι2 _ = refl
ix/=-sym ι1 ι3 _ = refl
ix/=-sym ι2 ι0 _ = refl
ix/=-sym ι2 ι1 _ = refl
ix/=-sym ι2 ι2 ()
ix/=-sym ι2 ι3 _ = refl
ix/=-sym ι3 ι0 _ = refl
ix/=-sym ι3 ι1 _ = refl
ix/=-sym ι3 ι2 _ = refl
ix/=-sym ι3 ι3 ()

vsel : {A : Set} -> Ix -> Vector 4 A -> A
vsel ι0 (a ∷ b ∷ c ∷ d ∷ []) = a
vsel ι1 (a ∷ b ∷ c ∷ d ∷ []) = b
vsel ι2 (a ∷ b ∷ c ∷ d ∷ []) = c
vsel ι3 (a ∷ b ∷ c ∷ d ∷ []) = d

-- The jth column, the jth row and the (r,c) entry of a 4×4 matrix.
mcol : {A : Set} -> Ix -> Matrix 4 4 A -> Vector 4 A
mcol c (Matrix' cs) = vsel c cs

mrow : {A : Set} -> Ix -> Matrix 4 4 A -> Vector 4 A
mrow r (Matrix' cs) = vector-map (vsel r) cs

ment : {A : Set} -> Ix -> Ix -> Matrix 4 4 A -> A
ment r c m = vsel r (mcol c m)

-- ----------------------------------------------------------------------
-- * Sums of four terms
--
-- The shapes below are exactly those that the matrix product of
-- Quantum.Synthesis.Matrix produces: the sums are nested to the right
-- and the scalar from the right factor comes first.

sum4 : {A : Set} {{_ : SemiRing A}} -> A -> A -> A -> A -> A
sum4 a b c d = a + (b + (c + d))

-- Σₖ wₖ·(vₖ)†: the (r,c) entry of U†·U, for w the cth and v the rth
-- column of U.
ipc : {A : Set} {{_ : Ring A}} {{_ : Adjoint A}} -> Vector 4 A -> Vector 4 A -> A
ipc (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []) (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ []) =
  sum4 (w₀ * (v₀ †)) (w₁ * (v₁ †)) (w₂ * (v₂ †)) (w₃ * (v₃ †))

-- Σₖ (uₖ)†·wₖ: the (r,c) entry of U·U†, for u the cth and w the rth
-- row of U.
ipr : {A : Set} {{_ : Ring A}} {{_ : Adjoint A}} -> Vector 4 A -> Vector 4 A -> A
ipr (u₀ ∷ u₁ ∷ u₂ ∷ u₃ ∷ []) (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ []) =
  sum4 ((u₀ †) * w₀) ((u₁ †) * w₁) ((u₂ †) * w₂) ((u₃ †) * w₃)

-- The number of odd entries of a 4-vector over ℤ₂, modulo 2.
odd-count : Vector 4 Z2 -> Z2
odd-count (a ∷ b ∷ c ∷ d ∷ []) = sum4 a b c d

-- The number of positions at which two 4-vectors over ℤ₂ are both
-- odd, modulo 2.
meet-count : Vector 4 Z2 -> Vector 4 Z2 -> Z2
meet-count (a ∷ b ∷ c ∷ d ∷ []) (p ∷ q ∷ r ∷ s ∷ []) = sum4 (a * p) (b * q) (c * r) (d * s)

-- ----------------------------------------------------------------------
-- * Unitarity

-- A unitary matrix over 𝔻[i]. The paper's 𝒞𝒞𝒮 consists of unitaries;
-- the type Op does not, so this is carried as a hypothesis.
record IsUnitary (U : Op) : Set where
  constructor is-unitary
  field
    u-left : adjoint U * U ≡ 1#
    u-right : U * adjoint U ≡ 1#
open IsUnitary public

-- ----------------------------------------------------------------------
-- * Reading off the entries
--
-- The sixteen entries of U are variables here, so nothing in the rest
-- of the module ever takes a matrix apart.
--
-- Performance: the two lemmas about U†U and UU† are stated for an
-- ABSTRACT ring, not for 𝔻[i]. They are pure bookkeeping -- each entry
-- of the product is a four-term sum of products of entries -- and over
-- an abstract ring the conversion checker compares those sums
-- structurally. Over 𝔻[i] it would instead unfold every product and
-- sum into the dyadic arithmetic (a smart constructor with a stuck
-- parity test inside an eta record), which made this module miss the
-- twenty minute limit of agda-check.sh.

module EntriesR {A : Set} {{_ : Ring A}} {{_ : Adjoint A}}
                (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : A) where

  U : Matrix 4 4 A
  U = Matrix' ((a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) ∷ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ [])
             ∷ (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ []) ∷ (d₀ ∷ d₁ ∷ d₂ ∷ d₃ ∷ []) ∷ [])

  e-adjU : (r c : Ix) -> ment r c (adjoint U * U) ≡ ipc (mcol c U) (mcol r U)
  e-adjU ι0 ι0 = refl
  e-adjU ι0 ι1 = refl
  e-adjU ι0 ι2 = refl
  e-adjU ι0 ι3 = refl
  e-adjU ι1 ι0 = refl
  e-adjU ι1 ι1 = refl
  e-adjU ι1 ι2 = refl
  e-adjU ι1 ι3 = refl
  e-adjU ι2 ι0 = refl
  e-adjU ι2 ι1 = refl
  e-adjU ι2 ι2 = refl
  e-adjU ι2 ι3 = refl
  e-adjU ι3 ι0 = refl
  e-adjU ι3 ι1 = refl
  e-adjU ι3 ι2 = refl
  e-adjU ι3 ι3 = refl

  e-Uadj : (r c : Ix) -> ment r c (U * adjoint U) ≡ ipr (mrow c U) (mrow r U)
  e-Uadj ι0 ι0 = refl
  e-Uadj ι0 ι1 = refl
  e-Uadj ι0 ι2 = refl
  e-Uadj ι0 ι3 = refl
  e-Uadj ι1 ι0 = refl
  e-Uadj ι1 ι1 = refl
  e-Uadj ι1 ι2 = refl
  e-Uadj ι1 ι3 = refl
  e-Uadj ι2 ι0 = refl
  e-Uadj ι2 ι1 = refl
  e-Uadj ι2 ι2 = refl
  e-Uadj ι2 ι3 = refl
  e-Uadj ι3 ι0 = refl
  e-Uadj ι3 ι1 = refl
  e-Uadj ι3 ι2 = refl
  e-Uadj ι3 ι3 = refl

-- The 𝔻[i]-specific half: the (1,l)-residue and the lde of an entry.
module Entries (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : DComplex) where

  U : Op
  U = Matrix' ((a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) ∷ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ [])
             ∷ (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ []) ∷ (d₀ ∷ d₁ ∷ d₂ ∷ d₃ ∷ []) ∷ [])

  -- The four columns of U. They are named so that the lde4-k lemmas
  -- can be applied to them explicitly: with underscores the instance
  -- LamDenomExp (Vector 4 DComplex) is not determined.
  private
    cA cB cC cD : Vector 4 DComplex
    cA = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []
    cB = b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []
    cC = c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ []
    cD = d₀ ∷ d₁ ∷ d₂ ∷ d₃ ∷ []

  -- ρˡ₁(U) entrywise: the parity of the Gaussian integer γˡ·Uᵣ꜀.
  -- (Stated with the γ↑ of Kopt.Base, which is what residue1-matrix
  -- uses; γ↑ l = γ ↑ l is γ↑-↑ below.)
  e-res1 : (l : ℕ) (r c : Ix) ->
           ment r c (residue1-matrix l U) ≡ parityℤ[i] (to-whole (ment r c U * (γ↑ l)))
  e-res1 l ι0 ι0 = refl
  e-res1 l ι0 ι1 = refl
  e-res1 l ι0 ι2 = refl
  e-res1 l ι0 ι3 = refl
  e-res1 l ι1 ι0 = refl
  e-res1 l ι1 ι1 = refl
  e-res1 l ι1 ι2 = refl
  e-res1 l ι1 ι3 = refl
  e-res1 l ι2 ι0 = refl
  e-res1 l ι2 ι1 = refl
  e-res1 l ι2 ι2 = refl
  e-res1 l ι2 ι3 = refl
  e-res1 l ι3 ι0 = refl
  e-res1 l ι3 ι1 = refl
  e-res1 l ι3 ι2 = refl
  e-res1 l ι3 ι3 = refl

  -- The same at any n: ρₙ of the Gaussian integer γˡ·Uᵣ꜀. (e-res1 is
  -- the case n = 1, with parityℤ[i] where ρ 1 would carry a one-element
  -- vector; Kopt.PatternFacts needs n = 2, where the pattern search of
  -- Kopt.Patterns lives.)
  e-res : (n l : ℕ) (r c : Ix) ->
          ment r c (residue-matrix l n U) ≡ ρ n (to-whole (ment r c U * (γ↑ l)))
  e-res n l ι0 ι0 = refl
  e-res n l ι0 ι1 = refl
  e-res n l ι0 ι2 = refl
  e-res n l ι0 ι3 = refl
  e-res n l ι1 ι0 = refl
  e-res n l ι1 ι1 = refl
  e-res n l ι1 ι2 = refl
  e-res n l ι1 ι3 = refl
  e-res n l ι2 ι0 = refl
  e-res n l ι2 ι1 = refl
  e-res n l ι2 ι2 = refl
  e-res n l ι2 ι3 = refl
  e-res n l ι3 ι0 = refl
  e-res n l ι3 ι1 = refl
  e-res n l ι3 ι2 = refl
  e-res n l ι3 ι3 = refl

  -- Every entry has lde at most that of the matrix.
  e-lde : (r c : Ix) -> lde (ment r c U) Nat.≤ lde U
  e-lde ι0 ι0 = NatP.≤-trans (lde4-0 a₀ a₁ a₂ a₃) (lde4-0 cA cB cC cD)
  e-lde ι1 ι0 = NatP.≤-trans (lde4-1 a₀ a₁ a₂ a₃) (lde4-0 cA cB cC cD)
  e-lde ι2 ι0 = NatP.≤-trans (lde4-2 a₀ a₁ a₂ a₃) (lde4-0 cA cB cC cD)
  e-lde ι3 ι0 = NatP.≤-trans (lde4-3 a₀ a₁ a₂ a₃) (lde4-0 cA cB cC cD)
  e-lde ι0 ι1 = NatP.≤-trans (lde4-0 b₀ b₁ b₂ b₃) (lde4-1 cA cB cC cD)
  e-lde ι1 ι1 = NatP.≤-trans (lde4-1 b₀ b₁ b₂ b₃) (lde4-1 cA cB cC cD)
  e-lde ι2 ι1 = NatP.≤-trans (lde4-2 b₀ b₁ b₂ b₃) (lde4-1 cA cB cC cD)
  e-lde ι3 ι1 = NatP.≤-trans (lde4-3 b₀ b₁ b₂ b₃) (lde4-1 cA cB cC cD)
  e-lde ι0 ι2 = NatP.≤-trans (lde4-0 c₀ c₁ c₂ c₃) (lde4-2 cA cB cC cD)
  e-lde ι1 ι2 = NatP.≤-trans (lde4-1 c₀ c₁ c₂ c₃) (lde4-2 cA cB cC cD)
  e-lde ι2 ι2 = NatP.≤-trans (lde4-2 c₀ c₁ c₂ c₃) (lde4-2 cA cB cC cD)
  e-lde ι3 ι2 = NatP.≤-trans (lde4-3 c₀ c₁ c₂ c₃) (lde4-2 cA cB cC cD)
  e-lde ι0 ι3 = NatP.≤-trans (lde4-0 d₀ d₁ d₂ d₃) (lde4-3 cA cB cC cD)
  e-lde ι1 ι3 = NatP.≤-trans (lde4-1 d₀ d₁ d₂ d₃) (lde4-3 cA cB cC cD)
  e-lde ι2 ι3 = NatP.≤-trans (lde4-2 d₀ d₁ d₂ d₃) (lde4-3 cA cB cC cD)
  e-lde ι3 ι3 = NatP.≤-trans (lde4-3 d₀ d₁ d₂ d₃) (lde4-3 cA cB cC cD)

-- ----------------------------------------------------------------------
-- ** The same facts for an arbitrary matrix

-- A 4×4 matrix is the matrix of its sixteen entries.
matrix-η : {A : Set} (M : Matrix 4 4 A) ->
           M ≡ Matrix' ((ment ι0 ι0 M ∷ ment ι1 ι0 M ∷ ment ι2 ι0 M ∷ ment ι3 ι0 M ∷ [])
                      ∷ (ment ι0 ι1 M ∷ ment ι1 ι1 M ∷ ment ι2 ι1 M ∷ ment ι3 ι1 M ∷ [])
                      ∷ (ment ι0 ι2 M ∷ ment ι1 ι2 M ∷ ment ι2 ι2 M ∷ ment ι3 ι2 M ∷ [])
                      ∷ (ment ι0 ι3 M ∷ ment ι1 ι3 M ∷ ment ι2 ι3 M ∷ ment ι3 ι3 M ∷ []) ∷ [])
matrix-η (Matrix' ((a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []) ∷ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ [])
                 ∷ (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ []) ∷ (d₀ ∷ d₁ ∷ d₂ ∷ d₃ ∷ []) ∷ [])) = refl

private
  module WR {A : Set} {{_ : Ring A}} {{_ : Adjoint A}} (M : Matrix 4 4 A) where
    open module ER = EntriesR
      (ment ι0 ι0 M) (ment ι1 ι0 M) (ment ι2 ι0 M) (ment ι3 ι0 M)
      (ment ι0 ι1 M) (ment ι1 ι1 M) (ment ι2 ι1 M) (ment ι3 ι1 M)
      (ment ι0 ι2 M) (ment ι1 ι2 M) (ment ι2 ι2 M) (ment ι3 ι2 M)
      (ment ι0 ι3 M) (ment ι1 ι3 M) (ment ι2 ι3 M) (ment ι3 ι3 M) public

  module WD (M : Op) where
    open module ED = Entries
      (ment ι0 ι0 M) (ment ι1 ι0 M) (ment ι2 ι0 M) (ment ι3 ι0 M)
      (ment ι0 ι1 M) (ment ι1 ι1 M) (ment ι2 ι1 M) (ment ι3 ι1 M)
      (ment ι0 ι2 M) (ment ι1 ι2 M) (ment ι2 ι2 M) (ment ι3 ι2 M)
      (ment ι0 ι3 M) (ment ι1 ι3 M) (ment ι2 ι3 M) (ment ι3 ι3 M) public

entry-adjU′ : {A : Set} {{_ : Ring A}} {{_ : Adjoint A}} (M : Matrix 4 4 A) (r c : Ix) ->
             ment r c (adjoint M * M) ≡ ipc (mcol c M) (mcol r M)
entry-adjU′ M r c = subst (λ N -> ment r c (adjoint N * N) ≡ ipc (mcol c N) (mcol r N))
                         (sym (matrix-η M)) (WR.e-adjU M r c)

entry-Uadj′ : {A : Set} {{_ : Ring A}} {{_ : Adjoint A}} (M : Matrix 4 4 A) (r c : Ix) ->
             ment r c (M * adjoint M) ≡ ipr (mrow c M) (mrow r M)
entry-Uadj′ M r c = subst (λ N -> ment r c (N * adjoint N) ≡ ipr (mrow c N) (mrow r N))
                          (sym (matrix-η M)) (WR.e-Uadj M r c)

-- The two powers of γ agree: the γ↑ of Kopt.Base and the _↑_ of
-- Kopt.Properties.Gamma are the same structural power.
γ↑-↑ : (l : ℕ) -> (DComplex ∋ γ↑ l) ≡ (γ {DComplex}) ↑ l
γ↑-↑ zero = refl
γ↑-↑ (suc l) = cong (λ z -> γ * z) (γ↑-↑ l)

entry-res1′ : (M : Op) (l : ℕ) (r c : Ix) ->
             ment r c (residue1-matrix l M) ≡ parityℤ[i] (to-whole (ment r c M * (γ ↑ l)))
entry-res1′ M l r c =
  trans (subst (λ N -> ment r c (residue1-matrix l N)
                         ≡ parityℤ[i] (to-whole (ment r c N * (γ↑ l))))
               (sym (matrix-η M)) (WD.e-res1 M l r c))
        (cong (λ z -> parityℤ[i] (to-whole (ment r c M * z))) (γ↑-↑ l))

-- The same at any n, which is what a statement about the pattern search
-- of Kopt.Patterns needs (it works at n = 2).
entry-res′ : (M : Op) (n l : ℕ) (r c : Ix) ->
             ment r c (residue-matrix l n M) ≡ ρ n (to-whole (ment r c M * (γ ↑ l)))
entry-res′ M n l r c =
  trans (subst (λ N -> ment r c (residue-matrix l n N)
                         ≡ ρ n (to-whole (ment r c N * (γ↑ l))))
               (sym (matrix-η M)) (WD.e-res M n l r c))
        (cong (λ z -> ρ n (to-whole (ment r c M * z))) (γ↑-↑ l))

entry-lde′ : (M : Op) (r c : Ix) -> lde (ment r c M) Nat.≤ lde M
entry-lde′ M r c = subst (λ N -> lde (ment r c N) Nat.≤ lde N) (sym (matrix-η M))
                        (WD.e-lde M r c)

-- The interface is abstract. Every one of these four is an instance of
-- the sixteen-entry module Entries/EntriesR transported along matrix-η,
-- so unfolding one of them turns a matrix variable into sixteen
-- projections inside a four-term sum; Kopt.Unitary2 applies them about
-- fifty times, and with transparent bodies the conversion checker
-- rebuilds that term at every step of every equational chain (the same
-- reason Kopt.Descent.Mat4 hides its proofs). Only the statements are
-- ever needed.
abstract
  entry-adjU : {A : Set} {{_ : Ring A}} {{_ : Adjoint A}} (M : Matrix 4 4 A) (r c : Ix) ->
               ment r c (adjoint M * M) ≡ ipc (mcol c M) (mcol r M)
  entry-adjU = entry-adjU′

  entry-Uadj : {A : Set} {{_ : Ring A}} {{_ : Adjoint A}} (M : Matrix 4 4 A) (r c : Ix) ->
               ment r c (M * adjoint M) ≡ ipr (mrow c M) (mrow r M)
  entry-Uadj = entry-Uadj′

  entry-res1 : (M : Op) (l : ℕ) (r c : Ix) ->
               ment r c (residue1-matrix l M) ≡ parityℤ[i] (to-whole (ment r c M * (γ ↑ l)))
  entry-res1 = entry-res1′

  entry-res : (M : Op) (n l : ℕ) (r c : Ix) ->
              ment r c (residue-matrix l n M) ≡ ρ n (to-whole (ment r c M * (γ ↑ l)))
  entry-res = entry-res′

  entry-lde : (M : Op) (r c : Ix) -> lde (ment r c M) Nat.≤ lde M
  entry-lde = entry-lde′

-- ----------------------------------------------------------------------
-- ** The entries of the identity matrix

ment-1-diag : {A : Set} {{_ : Ring A}} (c : Ix) -> ment c c (1# {A = Matrix 4 4 A}) ≡ 1#
ment-1-diag ι0 = refl
ment-1-diag ι1 = refl
ment-1-diag ι2 = refl
ment-1-diag ι3 = refl

ment-1-off : {A : Set} {{_ : Ring A}} (r c : Ix) -> ix/= r c ≡ true ->
             ment r c (1# {A = Matrix 4 4 A}) ≡ 0#
ment-1-off ι0 ι0 ()
ment-1-off ι0 ι1 _ = refl
ment-1-off ι0 ι2 _ = refl
ment-1-off ι0 ι3 _ = refl
ment-1-off ι1 ι0 _ = refl
ment-1-off ι1 ι1 ()
ment-1-off ι1 ι2 _ = refl
ment-1-off ι1 ι3 _ = refl
ment-1-off ι2 ι0 _ = refl
ment-1-off ι2 ι1 _ = refl
ment-1-off ι2 ι2 ()
ment-1-off ι2 ι3 _ = refl
ment-1-off ι3 ι0 _ = refl
ment-1-off ι3 ι1 _ = refl
ment-1-off ι3 ι2 _ = refl
ment-1-off ι3 ι3 ()

-- ----------------------------------------------------------------------
-- * The four consequences of unitarity

-- Σₖ Uₖ꜀·(Uₖ꜀)† = 1.
u-col : (U : Op) -> adjoint U * U ≡ 1# -> (c : Ix) -> ipc (mcol c U) (mcol c U) ≡ 1#
u-col U h c = trans (sym (entry-adjU U c c)) (trans (cong (ment c c) h) (ment-1-diag c))

-- Σₖ Uₖ꜀·(Uₖᵣ)† = 0 for r ≠ c.
o-col : (U : Op) -> adjoint U * U ≡ 1# -> (r c : Ix) -> ix/= r c ≡ true ->
        ipc (mcol c U) (mcol r U) ≡ 0#
o-col U h r c d = trans (sym (entry-adjU U r c)) (trans (cong (ment r c) h) (ment-1-off r c d))

-- Σₖ (Uᵣₖ)†·Uᵣₖ = 1.
u-row : (U : Op) -> U * adjoint U ≡ 1# -> (r : Ix) -> ipr (mrow r U) (mrow r U) ≡ 1#
u-row U h r = trans (sym (entry-Uadj U r r)) (trans (cong (ment r r) h) (ment-1-diag r))

-- Σₖ (U꜀ₖ)†·Uᵣₖ = 0 for r ≠ c.
o-row : (U : Op) -> U * adjoint U ≡ 1# -> (r c : Ix) -> ix/= r c ≡ true ->
        ipr (mrow c U) (mrow r U) ≡ 0#
o-row U h r c d = trans (sym (entry-Uadj U r c)) (trans (cong (ment r c) h) (ment-1-off r c d))

