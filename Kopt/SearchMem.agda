-- The permutations that the pattern search returns lie in all-perms.
--
-- The search of Kopt.Patterns picks a left and a right permutation out of
-- all-perms and reports the pattern it found; the caller learns nothing
-- else about them. A proof about the operator that the algorithm builds
-- from the level data needs their membership in all-perms, because that
-- is what makes Table I apply to them (Kopt.CircuitSem) and what lets the
-- numeral and Pos indexings be compared (Kopt.PermIndex).
--
-- The search is a structural recursion written with auxiliary functions
-- taking the scrutinee as an argument, rather than with `with`, which is
-- what makes this induction possible at all.

{-# OPTIONS --without-K --safe #-}

module Kopt.SearchMem where

open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; subst)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Permutations using (Tuple4 ; all-perms ; perm-inverse)
open import Kopt.Patterns using (SixCases)
import Kopt.Patterns as P
open import Kopt.Descent using (_∈ˡ_ ; here ; there ; ∈-map)

open P.Search using (Enc4 ; Found ; search-x ; search-x-aux ; search-y ; search-y-aux
                  ; case-of-code ; lar-code ; pattern-codes ; cols-table)

-- ----------------------------------------------------------------------
-- * The inner loop

-- search-y returns the left permutation it was given, and a right
-- permutation from the table it was given.
search-y-∈ : (x xi : Tuple4) (tbl : List (Tuple4 × Enc4)) {p : SixCases} {x' y' : Tuple4} ->
             search-y x xi tbl ≡ just (p , x' , y') ->
             (x' ≡ x) × (y' ∈ˡ List.map proj₁ tbl)
search-y-∈ x xi ((y , e) ∷ rest) {p} {x'} {y'} eq =
  aux (case-of-code (lar-code e xi) pattern-codes) eq
  where
    aux : (c : Maybe SixCases) ->
          search-y-aux c x xi y rest ≡ just (p , x' , y') ->
          (x' ≡ x) × (y' ∈ˡ List.map proj₁ ((y , e) ∷ rest))
    aux (just q) refl = refl , here
    aux nothing ee = proj₁ rec , there (proj₂ rec)
      where
        rec : (x' ≡ x) × (y' ∈ˡ List.map proj₁ rest)
        rec = search-y-∈ x xi rest ee

-- ----------------------------------------------------------------------
-- * The outer loop

search-x-∈ : (xs : List Tuple4) (tbl : List (Tuple4 × Enc4)) {p : SixCases} {x' y' : Tuple4} ->
             search-x xs tbl ≡ just (p , x' , y') ->
             (x' ∈ˡ xs) × (y' ∈ˡ List.map proj₁ tbl)
search-x-∈ (x ∷ xs) tbl {p} {x'} {y'} eq =
  aux (search-y x (perm-inverse x) tbl) refl eq
  where
    -- The value dispatched on is accompanied by its equation: abstracting
    -- it away otherwise loses the connection to the inner search, and the
    -- membership of the right permutation comes from exactly that.
    aux : (r : Maybe Found) -> search-y x (perm-inverse x) tbl ≡ r ->
          search-x-aux r xs tbl ≡ just (p , x' , y') ->
          (x' ∈ˡ (x ∷ xs)) × (y' ∈ˡ List.map proj₁ tbl)
    aux (just (q , a , b)) er refl =
      subst (λ z -> z ∈ˡ (x ∷ xs)) (sym (proj₁ hit)) here , proj₂ hit
      where
        hit : (x' ≡ x) × (y' ∈ˡ List.map proj₁ tbl)
        hit = search-y-∈ x (perm-inverse x) tbl er
    aux nothing er ee = there (proj₁ rec) , proj₂ rec
      where
        rec : (x' ∈ˡ xs) × (y' ∈ˡ List.map proj₁ tbl)
        rec = search-x-∈ xs tbl ee
