{-# OPTIONS --safe --without-K #-}

-- The second compound (exterior square) of a 4×4 matrix, indexed by the six
-- pairs i < j of Fin 4 in lexicographic order, and its multiplicative laws.
module GauInt.Matrix.Exterior where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_-_; _*_)
open import GauInt.Algebra using (module GaussianSolver)
open import GauInt.Matrix
open import GauInt.Matrix.Exterior.CauchyBinet using (cauchy-binet)
open import Finite.Check using (checkFin; allFin; lookupAll)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using ([]; _∷_; lookup)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl; cong₂)

pairs : Fin 6 → Fin 4 × Fin 4
pairs 0F = 0F , 1F
pairs 1F = 0F , 2F
pairs 2F = 0F , 3F
pairs 3F = 1F , 2F
pairs 4F = 1F , 3F
pairs 5F = 2F , 3F

wedge : Mat 4 → Mat 6
wedge M i j = M ir jr * M ic jc - M ir jc * M ic jr
  where
  ir = proj₁ (pairs i)
  ic = proj₂ (pairs i)
  jr = proj₁ (pairs j)
  jc = proj₂ (pairs j)

row6 : ZComplex → ZComplex → ZComplex → ZComplex → ZComplex → ZComplex → Fin 6 → ZComplex
row6 a b c d e f = lookup (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

wedge-cong : ∀ {M N : Mat 4} → M ≈ N → wedge M ≈ wedge N
wedge-cong h i j = cong₂ _-_
  (cong₂ _*_ (h (proj₁ (pairs i)) (proj₁ (pairs j))) (h (proj₂ (pairs i)) (proj₂ (pairs j))))
  (cong₂ _*_ (h (proj₁ (pairs i)) (proj₂ (pairs j))) (h (proj₂ (pairs i)) (proj₁ (pairs j))))

wedge-mul : ∀ M N → wedge (mul M N) ≈ mul (wedge M) (wedge N)
wedge-mul M N i j = cauchy-binet
  (M a 0F) (M a 1F) (M a 2F) (M a 3F)
  (M b 0F) (M b 1F) (M b 2F) (M b 3F)
  (N 0F c) (N 1F c) (N 2F c) (N 3F c)
  (N 0F d) (N 1F d) (N 2F d) (N 3F d)
  where
  a = proj₁ (pairs i)
  b = proj₂ (pairs i)
  c = proj₁ (pairs j)
  d = proj₂ (pairs j)

wedge-scale : ∀ z M → wedge (scale z M) ≈ scale (z * z) (wedge M)
wedge-scale z M i j = solve 5 (λ z a b c d →
  (z :* a) :* (z :* b) :- (z :* c) :* (z :* d) := (z :* z) :* (a :* b :- c :* d)) refl z
  (M (proj₁ (pairs i)) (proj₁ (pairs j))) (M (proj₂ (pairs i)) (proj₂ (pairs j)))
  (M (proj₁ (pairs i)) (proj₂ (pairs j))) (M (proj₂ (pairs i)) (proj₁ (pairs j)))
  where open GaussianSolver

wedge-id : wedge identity ≈ identity
wedge-id i = lookupAll (checkFin 6 _ (λ a → allFin 6 _ (λ b →
  wedge identity a b TC.≟ identity a b)) tt i)
