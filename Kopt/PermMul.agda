-- P_x · A · P_y is the reindexing of A that Kopt.Patterns computes.
--
-- This closes the gap between the two halves of the algorithm. The
-- residue search returns two permutations as ℕ tuples, together with
-- their membership in all-perms, and the level data records
-- permute-matrix x y of the residue matrix. The synthesis multiplies the
-- operator by the matrices of those permutations. That the two agree is
-- proved here, from the two one-sided lemmas -- gp-mul-right of
-- Kopt.Descent for the columns, perm-mul-left of Kopt.PermScatter for
-- the rows -- and the index dictionary of Kopt.PermIndex.

{-# OPTIONS --without-K --safe #-}

module Kopt.PermMul where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Properties
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Permutations
  using (Tuple4 ; sel ; all-perms ; perm-inverse ; perm-matrix-of ; unit-column)
open import Kopt.Patterns using (vsel4 ; select4 ; permute-matrix)
open import Kopt.Descent
  using (Op ; Pos ; p0 ; p1 ; p2 ; p3 ; Pos4 ; ph0 ; Phase4 ; selp ; selph ; inv4p
        ; distinct4p ; unit-vec ; gp-mat-of ; gp-mat ; GP ; gperm ; mcol4 ; gp-cols
        ; gp-mul-right ; smul ; mat4-≡ ; vec4-≡ ; _∈ˡ_ ; module M4)
open import Kopt.PermIndex
  using (vselp ; vsel4-pos ; sel-pos#4 ; select4-pos ; perm-pos ; perm-pos-eq
        ; perm-pos-inv ; perm-pos-distinct)
open import Kopt.PermScatter using (ph0s ; select4p ; perm-mul-left)
open import Kopt.GPData using (pos# ; pos#4)

open M4 using (smul-1)

-- ----------------------------------------------------------------------
-- * The permutation matrix of Kopt.Permutations is the generalized
--   permutation of Kopt.Descent with no phases

unit-column-vec : (q : Pos) -> unit-column (pos# q) 0 ≡ unit-vec q ph0
unit-column-vec p0 = refl
unit-column-vec p1 = refl
unit-column-vec p2 = refl
unit-column-vec p3 = refl

perm-mat-gp : (t : Pos4) -> perm-matrix-of (pos#4 t) ≡ gp-mat-of t ph0s
perm-mat-gp (a , b , c , d) =
  mat4-≡ (unit-column-vec a) (unit-column-vec b) (unit-column-vec c) (unit-column-vec d)

-- ----------------------------------------------------------------------
-- * The product, in Pos form

module _ (t s : Pos4) (ht : distinct4p t ≡ true) (hs : distinct4p s ≡ true) (A : Op) where
  private
    B : Op
    B = Matrix' ( select4p (inv4p t) (mcol4 p0 A)
                ∷ select4p (inv4p t) (mcol4 p1 A)
                ∷ select4p (inv4p t) (mcol4 p2 A)
                ∷ select4p (inv4p t) (mcol4 p3 A) ∷ [])

    -- the columns of B, read off
    mcol4-B : (q : Pos) -> mcol4 q B ≡ select4p (inv4p t) (mcol4 q A)
    mcol4-B p0 = refl
    mcol4-B p1 = refl
    mcol4-B p2 = refl
    mcol4-B p3 = refl

    col : (q : Pos) ->
          smul 1# (mcol4 (selp s q) B)
            ≡ select4p (inv4p t) (mcol4 (selp s q) A)
    col q = trans (smul-1 (mcol4 (selp s q) B)) (mcol4-B (selp s q))

  perm-mul-pos : gp-mat-of t ph0s * A * gp-mat-of s ph0s
                   ≡ Matrix' ( select4p (inv4p t) (mcol4 (selp s p0) A)
                             ∷ select4p (inv4p t) (mcol4 (selp s p1) A)
                             ∷ select4p (inv4p t) (mcol4 (selp s p2) A)
                             ∷ select4p (inv4p t) (mcol4 (selp s p3) A) ∷ [])
  perm-mul-pos =
    trans (cong (λ m -> m * gp-mat-of s ph0s) (perm-mul-left t ht A))
          (trans (gp-mul-right B (gperm s ph0s hs))
                 (mat4-≡ (col p0) (col p1) (col p2) (col p3)))

-- ----------------------------------------------------------------------
-- * The same for the permutations the search returns

mcol4-vselp : (q : Pos) (A : Op) -> mcol4 q A ≡ vselp q (unMatrix A)
mcol4-vselp p0 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl
mcol4-vselp p1 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl
mcol4-vselp p2 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl
mcol4-vselp p3 (Matrix' (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ [])) = refl

-- permute-matrix, written in Pos form. This is the step that needs the
-- memberships: perm-inverse searches the numeral tuple and does not
-- reduce until the permutation is known, while inv4p reads a table.
permute-form : (x y : Tuple4) (mx : x ∈ˡ all-perms) (my : y ∈ˡ all-perms) (A : Op) ->
               permute-matrix x y A
                 ≡ Matrix'
                     ( select4p (inv4p (perm-pos x mx)) (mcol4 (selp (perm-pos y my) p0) A)
                     ∷ select4p (inv4p (perm-pos x mx)) (mcol4 (selp (perm-pos y my) p1) A)
                     ∷ select4p (inv4p (perm-pos x mx)) (mcol4 (selp (perm-pos y my) p2) A)
                     ∷ select4p (inv4p (perm-pos x mx)) (mcol4 (selp (perm-pos y my) p3) A) ∷ [])
permute-form x y mx my A = mat4-≡ (colf p0) (colf p1) (colf p2) (colf p3)
  where
    tx : Pos4
    tx = perm-pos x mx
    ty : Pos4
    ty = perm-pos y my

    -- the column index, in Pos form
    ix : (k : Pos) -> sel y (pos# k) ≡ pos# (selp ty k)
    ix k = trans (cong (λ u -> sel u (pos# k)) (perm-pos-eq y my)) (sel-pos#4 ty k)

    colv : (k : Pos) -> vsel4 (unMatrix A) (sel y (pos# k)) ≡ mcol4 (selp ty k) A
    colv k = trans (cong (vsel4 (unMatrix A)) (ix k))
                   (trans (vsel4-pos (selp ty k) (unMatrix A))
                          (sym (mcol4-vselp (selp ty k) A)))

    colf : (k : Pos) -> select4 (perm-inverse x) (vsel4 (unMatrix A) (sel y (pos# k)))
                          ≡ select4p (inv4p tx) (mcol4 (selp ty k) A)
    colf k = trans (cong (select4 (perm-inverse x)) (colv k))
                   (trans (cong (λ u -> select4 u (mcol4 (selp ty k) A)) (perm-pos-inv x mx))
                          (select4-pos (inv4p tx) (mcol4 (selp ty k) A)))

-- P_x·A·P_y is the reindexing of A that the level data records.
perm-mul : (x y : Tuple4) (mx : x ∈ˡ all-perms) (my : y ∈ˡ all-perms) (A : Op) ->
           perm-matrix-of x * A * perm-matrix-of y ≡ permute-matrix x y A
perm-mul x y mx my A =
  trans (cong₂ (λ m n -> m * A * n) lhsx lhsy)
        (trans (perm-mul-pos (perm-pos x mx) (perm-pos y my)
                             (perm-pos-distinct x mx) (perm-pos-distinct y my) A)
               (sym (permute-form x y mx my A)))
  where
    lhsx : perm-matrix-of x ≡ gp-mat-of (perm-pos x mx) ph0s
    lhsx = trans (cong perm-matrix-of (perm-pos-eq x mx)) (perm-mat-gp (perm-pos x mx))
    lhsy : perm-matrix-of y ≡ gp-mat-of (perm-pos y my) ph0s
    lhsy = trans (cong perm-matrix-of (perm-pos-eq y my)) (perm-mat-gp (perm-pos y my))
