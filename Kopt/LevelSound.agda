-- What the level data says about the operator.
--
-- lemma-six returns, for an operator A of positive lde, a pattern and two
-- permutations, packed as LevelData. The algorithm then works with
-- B = L·A·R for the Table I circuits L and R of those permutations, and
-- with the residue matrix lev-res that the level data records. This module
-- proves that B is what it is meant to be:
--
--   * the two permutations lie in all-perms (Kopt.SearchMem), so Table I
--     applies to them (Kopt.CircuitSem) and B is the reindexing of A that
--     the level data names (Kopt.PermMul),
--   * the residue matrices of B are the recorded ones (Kopt.ResPerm and
--     rho2-integral for ρ₂, Kopt.PatternFacts for ρ₁, where the pattern
--     comes from the exhaustive check),
--   * B has the same lde as A (Remark II.10, both sides), and is unitary.
--
-- Every one of the six cases of Section IV B starts from this.

{-# OPTIONS --without-K --safe #-}

module Kopt.LevelSound where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base as List using (List)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates using (Circuit ; ⟦_⟧)
open import Kopt.Permutations using (Tuple4 ; all-perms ; perm-circuit-of ; perm-matrix-of)
open import Kopt.Patterns
  using (SixCases ; LevelData ; level-data ; lev-lde ; lev-pat ; lev-x ; lev-y ; lev-res
        ; lev-lcir ; lev-rcir ; level-at ; pattern-matrix ; permute-matrix ; rho2-of
        ; integral-matrix ; rows-4)
import Kopt.Patterns as P
open import Kopt.Descent using (Op ; _∈ˡ_ ; mat-*-assoc)
open import Kopt.Unitary using (IsUnitary)
open import Kopt.MatAdj using (unitary-*)
open import Kopt.Optimality using (remark-II-10 ; remark-II-10-right)
open import Kopt.GateUnitary using (circuit-unitary)
open import Kopt.CircuitSem using (perm-sem ; perm-kfree)
open import Kopt.ResPerm using (res-permute ; res1-permute)
open import Kopt.PermMul using (perm-mul)
open import Kopt.SearchMem using (search-x-∈)
open import Kopt.PatternFacts using (search-of ; level-at-suc ; rho2-integral ; level-sound-pos)

private
  -- map proj₁ (cols-table rs) is all-perms: cols-table pairs each
  -- permutation of the literal list with a code, and the list is short
  -- enough that this is a reduction.
  cols-table-perms : (rs : Vector 4 (Vector 4 Z2)) ->
                     List.map proj₁ (P.Search.cols-table rs) ≡ all-perms
  cols-table-perms rs = refl

-- ----------------------------------------------------------------------
-- * The level data of an operator of positive lde

-- The memberships, with every matrix a variable. Stated over the operator
-- itself instead, the dispatch below would substitute
-- level-data … (permute-matrix x y (rho2-of (integral-matrix l A))) for
-- the level data, and the checker would unfold that 𝔻[i] matrix: 560 s
-- and four gigabytes, against 20 s here.
private
  search-mem : (k : ℕ) (ld : LevelData) (R : Matrix 4 4 Z2) (W : Matrix 4 4 ZComplex)
               (r : Maybe P.Search.Found) -> search-of R ≡ r ->
               P.Level.level-from-s (suc k) r W ≡ just ld ->
               (lev-x ld ∈ˡ all-perms) × (lev-y ld ∈ˡ all-perms)
  search-mem k ld R W nothing er ()
  search-mem k ld R W (just (p , x , y)) er refl =
    proj₁ parts , subst (λ zs -> y ∈ˡ zs) (cols-table-perms (rows-4 R)) (proj₂ parts)
    where
      parts : (x ∈ˡ all-perms) × (y ∈ˡ List.map proj₁ (P.Search.cols-table (rows-4 R)))
      parts = search-x-∈ all-perms (P.Search.cols-table (rows-4 R)) er

module _ (A : Op) (hu : IsUnitary A) (k : ℕ) (ld : LevelData)
         (hl : lde A ≡ suc k) (he : level-at (suc k) A ≡ just ld) where
  private
    R : Matrix 4 4 Z2
    R = residue1-matrix (suc k) A

    W : Matrix 4 4 ZComplex
    W = integral-matrix (suc k) A

    from-s : P.Level.level-from-s (suc k) (search-of R) W ≡ just ld
    from-s = trans (sym (level-at-suc A k)) he

  -- The two permutations come from all-perms.
  lev-x-∈ : lev-x ld ∈ˡ all-perms
  lev-x-∈ = proj₁ (search-mem k ld R W (search-of R) refl from-s)

  lev-y-∈ : lev-y ld ∈ˡ all-perms
  lev-y-∈ = proj₂ (search-mem k ld R W (search-of R) refl from-s)

  private
    -- the recorded residue matrix, again with W a variable
    level-res : (r : Maybe P.Search.Found) ->
                P.Level.level-from-s (suc k) r W ≡ just ld ->
                lev-res ld ≡ permute-matrix (lev-x ld) (lev-y ld) (rho2-of W)
    level-res nothing ()
    level-res (just (p , x , y)) refl = refl

  -- The operator the algorithm passes on.
  B : Op
  B = ⟦ lev-lcir ld ⟧ * A * ⟦ lev-rcir ld ⟧

  -- It is the reindexing of A that the level data names.
  B-perm : B ≡ permute-matrix (lev-x ld) (lev-y ld) A
  B-perm = trans (cong₂ (λ m n -> m * A * n)
                        (perm-sem (lev-x ld) lev-x-∈) (perm-sem (lev-y ld) lev-y-∈))
                 (perm-mul (lev-x ld) (lev-y ld) lev-x-∈ lev-y-∈ A)

  -- Its ρ₂ is the recorded one.
  res2-B : residue-matrix (suc k) 2 B ≡ lev-res ld
  res2-B =
    trans (cong (residue-matrix (suc k) 2) B-perm)
    (trans (res-permute (suc k) 2 (lev-x ld) (lev-y ld) A)
    (trans (cong (permute-matrix (lev-x ld) (lev-y ld)) (sym (rho2-integral (suc k) A)))
           (sym (level-res (search-of R) from-s))))

  -- Its ρ₁ is the pattern.
  res1-B : residue1-matrix (suc k) B ≡ pattern-matrix (lev-pat ld)
  res1-B =
    trans (cong (residue1-matrix (suc k)) B-perm)
    (trans (res1-permute (suc k) (lev-x ld) (lev-y ld) A)
           (proj₁ (level-sound-pos A hu k ld hl he)))

  -- It has the lde of A: both circuits are K-free (Remark II.10).
  lde-B : lde B ≡ suc k
  lde-B =
    trans (cong lde (mat-*-assoc ⟦ lev-lcir ld ⟧ A ⟦ lev-rcir ld ⟧))
    (trans (remark-II-10 (lev-lcir ld) (perm-kfree (lev-x ld) lev-x-∈) (A * ⟦ lev-rcir ld ⟧))
    (trans (remark-II-10-right (lev-rcir ld) (perm-kfree (lev-y ld) lev-y-∈) A) hl))

  -- And it is unitary.
  unitary-B : IsUnitary B
  unitary-B =
    unitary-* (unitary-* (circuit-unitary (lev-lcir ld)) hu) (circuit-unitary (lev-rcir ld))
