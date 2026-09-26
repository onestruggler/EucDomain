{-# OPTIONS --safe --without-K #-}

-- Pointwise proof views of EucDomain's column-major matrices.
module GauInt.Matrix.Euc where
open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra using (*-comm; +-identityʳ)
open import GauInt.Matrix
import Quantum.Synthesis.Matrix as E
open import Quantum.Synthesis.Ring using (RingCplx; AdjointCplx)
open import Instances using (Ringℤ; Adjointℤ)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_; tabulate; lookup; map)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup; lookup-map; lookup-replicate; lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

Matrix : ℕ → ℕ → Set
Matrix m n = E.Matrix m n ZComplex

pack : ∀ {C : Set} {m n} → (Fin m → Fin n → C) → E.Matrix m n C
pack M = E.Matrix' (tabulate (λ j → tabulate (λ i → M i j)))

view : ∀ {C : Set} {m n} → E.Matrix m n C → Fin m → Fin n → C
view A i j = lookup (lookup (E.unMatrix A) j) i

view-pack : ∀ {C : Set} {m n} (M : Fin m → Fin n → C) i j → view (pack M) i j ≡ M i j
view-pack M i j = trans (cong (λ column → lookup column i)
  (lookup∘tabulate (λ j → tabulate (λ i → M i j)) j)) (lookup∘tabulate (λ i → M i j) i)

pack-view : ∀ {C : Set} {m n} (A : E.Matrix m n C) → pack (view A) ≡ A
pack-view (E.Matrix' columns) = cong E.Matrix' (trans
  (Data.Vec.Properties.tabulate-cong (λ j → tabulate∘lookup (lookup columns j)))
  (tabulate∘lookup columns))

map-view : ∀ {C D : Set} {m n} (f : C → D) (A : E.Matrix m n C) i j →
  view (E.matrix-map f A) i j ≡ f (view A i j)
map-view f (E.Matrix' columns) i j = trans
  (cong (λ column → lookup column i) (lookup-map j (map f) columns))
  (lookup-map i f (lookup columns j))

ext : ∀ {C : Set} {m n} {A B : E.Matrix m n C} →
  (∀ i j → view A i j ≡ view B i j) → A ≡ B
ext {A = A} {B} h = trans (sym (pack-view A))
  (trans (cong E.Matrix' (Data.Vec.Properties.tabulate-cong
    (λ j → Data.Vec.Properties.tabulate-cong (λ i → h i j)))) (pack-view B))

map-cong : ∀ {C D : Set} {m n} (f g : C → D) → (∀ x → f x ≡ g x) →
  (A : E.Matrix m n C) → E.matrix-map f A ≡ E.matrix-map g A
map-cong f g h A = ext {A = E.matrix-map f A} {B = E.matrix-map g A} (λ i j →
  trans (map-view f A i j) (trans (h (view A i j)) (sym (map-view g A i j))))

map-compose : ∀ {C D F : Set} {m n} (f : D → F) (g : C → D) (A : E.Matrix m n C) →
  E.matrix-map f (E.matrix-map g A) ≡ E.matrix-map (λ x → f (g x)) A
map-compose f g A = ext {A = E.matrix-map f (E.matrix-map g A)} {B = E.matrix-map (λ x → f (g x)) A}
  (λ i j → trans (map-view f (E.matrix-map g A) i j)
    (trans (cong f (map-view g A i j)) (sym (map-view (λ x → f (g x)) A i j))))

multiply : ∀ {m n p} → Matrix m n → Matrix n p → Matrix m p
multiply = E._·*·_

scaleMatrix : ∀ {m n} → ZComplex → Matrix m n → Matrix m n
scaleMatrix = E._scalarmult_

scale-view : ∀ {m n} z (A : Matrix m n) i j → view (scaleMatrix z A) i j ≡ z * view A i j
scale-view z A = map-view (z *_) A

private
  columnProduct : ∀ {m n} → Vec (Vec ZComplex m) n → Vec ZComplex n → Vec ZComplex m
  columnProduct columns weights = lookup (E.unMatrix (multiply (E.Matrix' columns) (E.Matrix' (weights ∷ [])))) zero

  column-sum : ∀ {m n} (columns : Vec (Vec ZComplex m) n) weights i →
    lookup (columnProduct columns weights) i ≡ sum (λ k → lookup (lookup columns k) i * lookup weights k)
  column-sum [] [] i = lookup-replicate i 0#
  column-sum (h ∷ []) (k ∷ []) i = trans (lookup-map i (k *_) h)
    (trans (*-comm k (lookup h i)) (sym (+-identityʳ (lookup h i * k))))
  column-sum (h ∷ t@(_ ∷ _)) (k ∷ s) i = trans
    (lookup-zipWith _+_ i (map (k *_) h) (columnProduct t s))
    (cong₂ _+_ (trans (lookup-map i (k *_) h) (*-comm k (lookup h i))) (column-sum t s i))

  product-column : ∀ {m n p} (columns : Vec (Vec ZComplex m) n) (right : Vec (Vec ZComplex n) p) j →
    lookup (E.unMatrix (multiply (E.Matrix' columns) (E.Matrix' right))) j ≡ columnProduct columns (lookup right j)
  product-column columns (h ∷ t) zero = refl
  product-column columns (h ∷ t) (suc j) = product-column columns t j

multiply-view : ∀ {m n p} (A : Matrix m n) (B : Matrix n p) i j →
  view (multiply A B) i j ≡ sum (λ k → view A i k * view B k j)
multiply-view (E.Matrix' columns) (E.Matrix' right) i j = trans
  (cong (λ column → lookup column i) (product-column columns right j))
  (column-sum columns (lookup right j) i)
