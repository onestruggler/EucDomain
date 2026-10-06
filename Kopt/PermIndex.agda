-- The two ways this development indexes a permutation of the four
-- coordinates, and the dictionary between them.
--
-- Kopt.Descent indexes by Pos, a four-element datatype: selp t p0
-- reduces even when the permutation t is a variable, which is why the
-- group laws and gp-mul-right there are proved once, symbolically.
-- Kopt.Permutations and Kopt.Patterns index by Tuple4 = ℕ × ℕ × ℕ × ℕ,
-- because Table I and the residue search are stated over numerals: there
-- `sel y k` with y a variable never reduces, and nothing about a
-- permutation computes until it is known.
--
-- A proof about the operator the algorithm builds has to cross between
-- the two, since the search returns a Tuple4 and the matrix algebra
-- lives in Pos. The crossing is cheap, because the search also returns
-- the membership of its permutation in all-perms, and the 24 tables
-- below are a refl apiece. They are also the check that the two inverse
-- conventions agree -- perm-inverse searches the ℕ tuple, inv4p reads a
-- table of Pos.

{-# OPTIONS --without-K --safe #-}

module Kopt.PermIndex where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Permutations using (Tuple4 ; sel ; all-perms ; perm-inverse)
open import Kopt.Patterns using (vsel4 ; select4)
open import Kopt.Descent
  using (Pos ; p0 ; p1 ; p2 ; p3 ; Pos4 ; selp ; inv4p ; distinct4p
        ; _∈ˡ_ ; here ; there ; vec4-≡)
open import Kopt.GPData using (pos# ; pos#4)

-- ----------------------------------------------------------------------
-- * Selecting with a Pos

vselp : {A : Set} -> Pos -> Vector 4 A -> A
vselp p0 (a ∷ b ∷ c ∷ d ∷ []) = a
vselp p1 (a ∷ b ∷ c ∷ d ∷ []) = b
vselp p2 (a ∷ b ∷ c ∷ d ∷ []) = c
vselp p3 (a ∷ b ∷ c ∷ d ∷ []) = d

-- The numeral of a Pos selects the same entry. This is the lemma that
-- lets a numeral-indexed selection be rewritten into one that reduces.
vsel4-pos : {A : Set} (p : Pos) (v : Vector 4 A) -> vsel4 v (pos# p) ≡ vselp p v
vsel4-pos p0 (a ∷ b ∷ c ∷ d ∷ []) = refl
vsel4-pos p1 (a ∷ b ∷ c ∷ d ∷ []) = refl
vsel4-pos p2 (a ∷ b ∷ c ∷ d ∷ []) = refl
vsel4-pos p3 (a ∷ b ∷ c ∷ d ∷ []) = refl

-- Selecting from the numeral tuple of a Pos4 is selecting from the Pos4.
sel-pos#4 : (t : Pos4) (k : Pos) -> sel (pos#4 t) (pos# k) ≡ pos# (selp t k)
sel-pos#4 (a , b , c , d) p0 = refl
sel-pos#4 (a , b , c , d) p1 = refl
sel-pos#4 (a , b , c , d) p2 = refl
sel-pos#4 (a , b , c , d) p3 = refl

-- select4 along the numeral tuple of a Pos4, in Pos form.
select4-pos : {A : Set} (t : Pos4) (v : Vector 4 A) ->
              select4 (pos#4 t) v
                ≡ (vselp (selp t p0) v ∷ vselp (selp t p1) v
                 ∷ vselp (selp t p2) v ∷ vselp (selp t p3) v ∷ [])
select4-pos (a , b , c , d) v =
  vec4-≡ (vsel4-pos a v) (vsel4-pos b v) (vsel4-pos c v) (vsel4-pos d v)

-- ----------------------------------------------------------------------
-- * The 24 permutations of all-perms, as Pos4

perm-pos : (x : Tuple4) -> x ∈ˡ all-perms -> Pos4
perm-pos _ here = p0 , p1 , p2 , p3
perm-pos _ (there here) = p1 , p0 , p2 , p3
perm-pos _ (there (there here)) = p2 , p1 , p0 , p3
perm-pos _ (there (there (there here))) = p1 , p2 , p0 , p3
perm-pos _ (there (there (there (there here)))) = p2 , p0 , p1 , p3
perm-pos _ (there (there (there (there (there here))))) = p0 , p2 , p1 , p3
perm-pos _ (there (there (there (there (there (there here)))))) = p3 , p2 , p1 , p0
perm-pos _ (there (there (there (there (there (there (there here))))))) = p2 , p3 , p1 , p0
perm-pos _ (there (there (there (there (there (there (there (there here)))))))) = p2 , p1 , p3 , p0
perm-pos _ (there (there (there (there (there (there (there (there (there here))))))))) = p3 , p1 , p2 , p0
perm-pos _ (there (there (there (there (there (there (there (there (there (there here)))))))))) = p1 , p3 , p2 , p0
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = p1 , p2 , p3 , p0
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) = p3 , p0 , p1 , p2
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) = p0 , p3 , p1 , p2
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) = p0 , p1 , p3 , p2
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))) = p3 , p1 , p0 , p2
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))) = p1 , p3 , p0 , p2
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))) = p1 , p0 , p3 , p2
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))) = p3 , p0 , p2 , p1
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))) = p0 , p3 , p2 , p1
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))) = p0 , p2 , p3 , p1
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))) = p3 , p2 , p0 , p1
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))))) = p2 , p3 , p0 , p1
perm-pos _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))))) = p2 , p0 , p3 , p1

-- Both tables are refl in every one of the 24 cases, which is also the
-- check that the two inverse conventions agree: perm-inverse searches
-- the ℕ tuple, inv4p reads a Pos table.
perm-pos-eq : (x : Tuple4) (m : x ∈ˡ all-perms) -> x ≡ pos#4 (perm-pos x m)
perm-pos-eq _ here = refl
perm-pos-eq _ (there here) = refl
perm-pos-eq _ (there (there here)) = refl
perm-pos-eq _ (there (there (there here))) = refl
perm-pos-eq _ (there (there (there (there here)))) = refl
perm-pos-eq _ (there (there (there (there (there here))))) = refl
perm-pos-eq _ (there (there (there (there (there (there here)))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there here))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there here)))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there here))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there here)))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))))) = refl
perm-pos-eq _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))))) = refl

perm-pos-inv : (x : Tuple4) (m : x ∈ˡ all-perms) ->
               perm-inverse x ≡ pos#4 (inv4p (perm-pos x m))
perm-pos-inv _ here = refl
perm-pos-inv _ (there here) = refl
perm-pos-inv _ (there (there here)) = refl
perm-pos-inv _ (there (there (there here))) = refl
perm-pos-inv _ (there (there (there (there here)))) = refl
perm-pos-inv _ (there (there (there (there (there here))))) = refl
perm-pos-inv _ (there (there (there (there (there (there here)))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there here))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there here)))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there here))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there here)))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))))) = refl
perm-pos-inv _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))))) = refl

perm-pos-distinct : (x : Tuple4) (m : x ∈ˡ all-perms) -> distinct4p (perm-pos x m) ≡ true
perm-pos-distinct _ here = refl
perm-pos-distinct _ (there here) = refl
perm-pos-distinct _ (there (there here)) = refl
perm-pos-distinct _ (there (there (there here))) = refl
perm-pos-distinct _ (there (there (there (there here)))) = refl
perm-pos-distinct _ (there (there (there (there (there here))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there here)))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there here))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there here)))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there here))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there here)))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here)))))))))))))))))))))) = refl
perm-pos-distinct _ (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))))))))))))) = refl
