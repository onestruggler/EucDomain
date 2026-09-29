-- Residues commute with a permutation of the rows and columns.
--
-- The refinements of Section IV B work with ρˡ₂ of the operator that
-- lemma-six's two permutations produce, and the level data records the
-- permutation of ρˡ₂ of the operator itself (lev-res of Kopt.Patterns).
-- Those are the same thing: ρₙ is applied entrywise, and so is the
-- reindexing, so the two commute. That is this module.
--
-- It is the reindexing half of the statement. The other half -- that
-- permute-matrix x y M really is P_x·M·P_y -- is about the matrices of
-- Kopt.Permutations and is separate.

{-# OPTIONS --without-K --safe #-}

module Kopt.ResPerm where

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Permutations using (Tuple4 ; sel ; perm-inverse)
open import Kopt.Patterns using (vsel4 ; select4 ; permute-matrix ; R2)
open import Kopt.Descent using (Op ; vec4-≡ ; mat4-≡)

-- ----------------------------------------------------------------------
-- * Selection commutes with a map

-- vsel4's last clause returns the last entry, so this holds at every n,
-- in range or not -- which matters, because the index here is `sel y k`
-- with y a variable.
vsel4-map : {A B : Set} (f : A -> B) (v : Vector 4 A) (n : ℕ) ->
            vsel4 (vector-map f v) n ≡ f (vsel4 v n)
vsel4-map f (a ∷ b ∷ c ∷ d ∷ []) zero = refl
vsel4-map f (a ∷ b ∷ c ∷ d ∷ []) (suc zero) = refl
vsel4-map f (a ∷ b ∷ c ∷ d ∷ []) (suc (suc zero)) = refl
vsel4-map f (a ∷ b ∷ c ∷ d ∷ []) (suc (suc (suc n))) = refl

select4-map : {A B : Set} (f : A -> B) (s : Tuple4) (v : Vector 4 A) ->
              select4 s (vector-map f v) ≡ vector-map f (select4 s v)
select4-map f s v = vec4-≡ (vsel4-map f v (sel s 0)) (vsel4-map f v (sel s 1))
                           (vsel4-map f v (sel s 2)) (vsel4-map f v (sel s 3))

-- ----------------------------------------------------------------------
-- * Reindexing commutes with a map

permute-map : {A B : Set} (f : A -> B) (x y : Tuple4) (M : Matrix 4 4 A) ->
              permute-matrix x y (matrix-map f M) ≡ matrix-map f (permute-matrix x y M)
permute-map f x y (Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])) =
  mat4-≡ (col 0) (col 1) (col 2) (col 3)
  where
    cs : Vector 4 (Vector 4 _)
    cs = c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ []
    xi : Tuple4
    xi = perm-inverse x
    col : (k : ℕ) ->
          select4 xi (vsel4 (vector-map (vector-map f) cs) (sel y k))
            ≡ vector-map f (select4 xi (vsel4 cs (sel y k)))
    col k = trans (cong (select4 xi) (vsel4-map (vector-map f) cs (sel y k)))
                  (select4-map f xi (vsel4 cs (sel y k)))

-- ----------------------------------------------------------------------
-- * Residues commute with reindexing
--
-- residue-matrix is three entrywise maps: multiply by γˡ, take the whole
-- part, take ρₙ. (That is what the LamDenomExp, WholePart and matrix-map
-- instances of Kopt.Base and Quantum.Synthesis.Matrix unfold to.)

res-map : (l n : ℕ) (M : Op) ->
          residue-matrix l n M
            ≡ matrix-map (ρ n) (matrix-map to-whole (matrix-map (λ a -> a * γ↑ l) M))
res-map l n (Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])) = refl

res-permute : (l n : ℕ) (x y : Tuple4) (A : Op) ->
              residue-matrix l n (permute-matrix x y A)
                ≡ permute-matrix x y (residue-matrix l n A)
res-permute l n x y A =
  trans (res-map l n (permute-matrix x y A))
  (trans (cong (λ M -> matrix-map (ρ n) (matrix-map to-whole M))
               (sym (permute-map (λ a -> a * γ↑ l) x y A)))
  (trans (cong (matrix-map (ρ n)) (sym (permute-map to-whole x y (matrix-map (λ a -> a * γ↑ l) A))))
  (trans (sym (permute-map (ρ n) x y (matrix-map to-whole (matrix-map (λ a -> a * γ↑ l) A))))
         (cong (permute-matrix x y) (sym (res-map l n A))))))

-- The (1,l)-residue is the case n = 1, which residue1-matrix spells out
-- with parityℤ[i] instead of ρ 1.
res1-permute : (l : ℕ) (x y : Tuple4) (A : Op) ->
               residue1-matrix l (permute-matrix x y A)
                 ≡ permute-matrix x y (residue1-matrix l A)
res1-permute l x y A =
  trans (res1-map l (permute-matrix x y A))
  (trans (cong (λ M -> matrix-map parityℤ[i] (matrix-map to-whole M))
               (sym (permute-map (λ a -> a * γ↑ l) x y A)))
  (trans (cong (matrix-map parityℤ[i])
               (sym (permute-map to-whole x y (matrix-map (λ a -> a * γ↑ l) A))))
  (trans (sym (permute-map parityℤ[i] x y
                (matrix-map to-whole (matrix-map (λ a -> a * γ↑ l) A))))
         (cong (permute-matrix x y) (sym (res1-map l A))))))
  where
    res1-map : (l : ℕ) (M : Op) ->
               residue1-matrix l M
                 ≡ matrix-map parityℤ[i] (matrix-map to-whole (matrix-map (λ a -> a * γ↑ l) M))
    res1-map l (Matrix' (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ [])) = refl
