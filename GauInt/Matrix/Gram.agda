{-# OPTIONS --safe --without-K #-}

-- Matrix adjoints, row and column Gram matrices, and scaled Gram equations.
module GauInt.Matrix.Gram where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Matrix
open import GauInt.TwoPower using (twoPower; twoPower-add)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using () renaming (+-comm to nat+-comm)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

conj-sum : ∀ {n} (f : Fin n → ZComplex) → TC.adj (sum f) ≡ sum (λ i → TC.adj (f i))
conj-sum {zero} f = refl
conj-sum {suc n} f = trans (conj-add (f zero) (sum (λ i → f (suc i))))
  (cong (TC.adj (f zero) TC.+_) (conj-sum (λ i → f (suc i))))

adjoint-cong : ∀ {n} {M N : Mat n} → M ≈ N → adjoint M ≈ adjoint N
adjoint-cong h i j = cong TC.adj (h j i)

adjoint-mul : ∀ {n} (M N : Mat n) → adjoint (mul M N) ≈ mul (adjoint N) (adjoint M)
adjoint-mul M N i j = trans (conj-sum (λ k → M j k * N k i))
  (sum-cong (λ k → trans (conj-mul (M j k) (N k i)) (*-comm (TC.adj (M j k)) (TC.adj (N k i)))))

adjoint-scale : ∀ {n} z (M : Mat n) → adjoint (scale z M) ≈ scale (TC.adj z) (adjoint M)
adjoint-scale z M i j = conj-mul z (M j i)

gram-cong : ∀ {n} {M N : Mat n} → M ≈ N → gram M ≈ gram N
gram-cong {M = M} {N} h = mul-cong {A = M} {B = N} {C = adjoint M} {D = adjoint N} h (adjoint-cong h)

gram-scale : ∀ {n} z (M : Mat n) → gram (scale z M) ≈ scale (z * TC.adj z) (gram M)
gram-scale z M = ≈-trans
  (mul-cong {A = scale z M} {B = scale z M} ≈-refl (adjoint-scale z M))
  (≈-trans (mul-scaleˡ z M (scale (TC.adj z) (adjoint M)))
    (≈-trans (scale-cong z (mul-scaleʳ (TC.adj z) M (adjoint M)))
      (scale-scale z (TC.adj z) (gram M))))

gram-mul : ∀ {n} (M N : Mat n) → gram (mul M N) ≈ mul (mul M (gram N)) (adjoint M)
gram-mul M N = ≈-trans
  (mul-cong {A = mul M N} {B = mul M N} ≈-refl (adjoint-mul M N))
  (≈-trans (≈-sym (mul-assoc (mul M N) (adjoint N) (adjoint M)))
    (mul-cong {C = adjoint M} {D = adjoint M} (mul-assoc M N (adjoint N)) ≈-refl))

mul-unitary : ∀ {n} (M N : Mat n) a b →
  gram M ≈ scale (twoPower a) identity → gram N ≈ scale (twoPower b) identity →
  gram (mul M N) ≈ scale (twoPower (a + b)) identity
mul-unitary M N a b hm hn = ≈-trans (gram-mul M N)
  (≈-trans (mul-cong {C = adjoint M} {D = adjoint M}
    (mul-cong {A = M} {B = M} ≈-refl hn) ≈-refl)
    (≈-trans (mul-cong {C = adjoint M} {D = adjoint M}
      (≈-trans (mul-scaleʳ (twoPower b) M identity) (scale-cong (twoPower b) (mul-identity M))) ≈-refl)
      (≈-trans (mul-scaleˡ (twoPower b) M (adjoint M))
        (≈-trans (scale-cong (twoPower b) hm)
          (≈-trans (scale-scale (twoPower b) (twoPower a) identity)
            (λ i j → cong (_* identity i j) (trans (*-comm (twoPower b) (twoPower a)) (sym (twoPower-add a b)))))))))

adjoint-id : ∀ {n} → adjoint (identity {n}) ≈ identity
adjoint-id zero zero = refl
adjoint-id zero (suc j) = refl
adjoint-id (suc i) zero = refl
adjoint-id (suc i) (suc j) = adjoint-id i j

gram-id : ∀ {n} → gram (identity {n}) ≈ scale (twoPower 0) identity
gram-id {n} = ≈-trans (mul-cong {A = identity {n}} {B = identity {n}} ≈-refl adjoint-id)
  (≈-trans (identity-mul identity) (λ i j → sym (*-identityˡ (identity i j))))

-- Column Gram equations are transported explicitly. This module does not
-- assume a general square-matrix inverse theorem.
columnGram : ∀ {n} → Mat n → Mat n
columnGram M = gram (adjoint M)

columnGram-cong : ∀ {n} {M N : Mat n} → M ≈ N → columnGram M ≈ columnGram N
columnGram-cong {M = M} {N} h = gram-cong {M = adjoint M} {N = adjoint N} (adjoint-cong h)

columnGram-scale : ∀ {n} z (M : Mat n) → columnGram (scale z M) ≈ scale (z * TC.adj z) (columnGram M)
columnGram-scale z M = ≈-trans
  (gram-cong {M = adjoint (scale z M)} {N = scale (TC.adj z) (adjoint M)} (adjoint-scale z M))
  (≈-trans (gram-scale (TC.adj z) (adjoint M))
    (λ i j → cong (_* columnGram M i j)
      (trans (cong (TC.adj z *_) (conj-involutive z)) (*-comm (TC.adj z) z))))

columnGram-mul-unitary : ∀ {n} (M N : Mat n) a b →
  columnGram M ≈ scale (twoPower a) identity → columnGram N ≈ scale (twoPower b) identity →
  columnGram (mul M N) ≈ scale (twoPower (a + b)) identity
columnGram-mul-unitary M N a b hM hN = ≈-trans
  (gram-cong {M = adjoint (mul M N)} {N = mul (adjoint N) (adjoint M)} (adjoint-mul M N))
  (≈-trans (mul-unitary (adjoint N) (adjoint M) b a hN hM)
    (λ i j → cong (λ k → scale (twoPower k) identity i j) (nat+-comm b a)))

columnGram-id : ∀ {n} → columnGram (identity {n}) ≈ scale (twoPower 0) identity
columnGram-id {n} = ≈-trans (gram-cong {M = adjoint (identity {n})} {N = identity {n}} adjoint-id) gram-id

-- Bridge the column-Gram convention to the row Gram of the transpose.
column-transpose : ∀ {d} (M : Mat d) i j → columnGram M i j ≡ gram (transpose M) j i
column-transpose M i j = sum-cong λ k → trans
  (cong (TC.adj (M k i) *_) (conj-involutive (M k j))) (*-comm (TC.adj (M k i)) (M k j))

transpose-from-column : ∀ {d} (M : Mat d) n → columnGram M ≈ scale (twoPower n) identity →
  gram (transpose M) ≈ scale (twoPower n) identity
transpose-from-column M n h i j = trans (sym (column-transpose M j i))
  (trans (h j i) (cong (twoPower n *_) (delta-sym j i)))

column-from-transpose : ∀ {d} (M : Mat d) n → gram (transpose M) ≈ scale (twoPower n) identity →
  columnGram M ≈ scale (twoPower n) identity
column-from-transpose M n h i j = trans (column-transpose M i j)
  (trans (h j i) (cong (twoPower n *_) (delta-sym j i)))
