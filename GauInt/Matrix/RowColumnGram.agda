{-# OPTIONS --safe --without-K #-}

-- A square Gaussian matrix's row Gram determines its column Gram.
module GauInt.Matrix.RowColumnGram where
open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
open import GauInt.Algebra
open import GauInt.Matrix
open import GauInt.Matrix.Gram
open import GauInt.Matrix.Trace
open import GauInt.TwoPower using (twoPower; twoPower-real)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open GaussianSolver

product : ∀ {n} → Mat n → Mat n
product M = mul (adjoint M) M

column-product : ∀ {n} (M : Mat n) → columnGram M ≈ product M
column-product M = mul-cong {A = adjoint M} {B = adjoint M} ≈-refl (adjoint-twice M)

product-hermitian : ∀ {n} (M : Mat n) → adjoint (product M) ≈ product M
product-hermitian M = ≈-trans (adjoint-mul (adjoint M) M)
  (mul-cong {A = adjoint M} {B = adjoint M} ≈-refl (adjoint-twice M))

product-square : ∀ {n} (M : Mat n) a → gram M ≈ scale a identity → mul (product M) (product M) ≈ scale a (product M)
product-square M a h = ≈-trans (mul-assoc (adjoint M) M (product M))
  (≈-trans (mul-cong {A = adjoint M} {B = adjoint M} ≈-refl inner)
    (mul-scaleʳ a (adjoint M) M))
  where
  inner : mul M (product M) ≈ scale a M
  inner = ≈-trans (≈-sym (mul-assoc M (adjoint M) M))
    (≈-trans (mul-cong {C = M} {D = M} h ≈-refl)
      (≈-trans (mul-scaleˡ a identity M) (scale-cong a (identity-mul M))))

product-trace : ∀ {n} (M : Mat n) a → gram M ≈ scale a identity → trace (product M) ≡ a * trace (identity {n})
product-trace {n} M a h = trans (trace-mul (adjoint M) M) (trans (trace-cong h) (trace-scale a (identity {n})))

residual : ∀ {n} → Mat n → ZComplex → Mat n
residual M a = sub (product M) (scale a identity)

residual-hermitian : ∀ {n} (M : Mat n) a → TC.adj a ≡ a → adjoint (residual M a) ≈ residual M a
residual-hermitian M a ha i j = trans (conj-sub (product M j i) (scale a identity j i))
  (cong₂ _-_ (product-hermitian M i j)
    (trans (adjoint-scale a identity i j) (cong₂ _*_ ha (adjoint-id i j))))

residual-gram : ∀ {n} (M : Mat n) a → TC.adj a ≡ a → gram M ≈ scale a identity →
  gram (residual M a) ≈ sub (scale (a * a) identity) (scale a (product M))
residual-gram M a ha h i j = trans
  (mul-cong {A = E} {B = E} ≈-refl (residual-hermitian M a ha) i j)
  (trans (mul-sub-both C S C S i j)
    (trans (cong₂ _-_ (cong₂ _-_ (product-square M a h i j) (sc i j))
      (cong₂ _-_ (cs i j) (ss i j)))
      (solve 2 (λ x y → (x :- x) :- (x :- y) := y :- x) refl
        (scale a C i j) (scale (a * a) identity i j))))
  where
  C = product M
  S = scale a identity
  E = residual M a
  sc : mul S C ≈ scale a C
  sc = ≈-trans (mul-scaleˡ a identity C) (scale-cong a (identity-mul C))
  cs : mul C S ≈ scale a C
  cs = ≈-trans (mul-scaleʳ a C identity) (scale-cong a (mul-identity C))
  ss : mul S S ≈ scale (a * a) identity
  ss = ≈-trans (mul-scaleˡ a identity S)
    (≈-trans (scale-cong a (identity-mul S)) (scale-scale a a identity))

residual-trace-zero : ∀ {n} (M : Mat n) a → TC.adj a ≡ a → gram M ≈ scale a identity → trace (gram (residual M a)) ≡ 0#
residual-trace-zero {n} M a ha h = trans (trace-cong (residual-gram M a ha h))
  (trans (trace-sub (scale (a * a) (identity {n})) (scale a (product M)))
    (trans (cong₂ _-_ (trace-scale (a * a) (identity {n}))
      (trans (trace-scale a (product M)) (cong (a *_) (product-trace M a h))))
      (solve 2 (λ a t → (a :* a) :* t :- a :* (a :* t) := con 0#) refl a (trace (identity {n})))))

row-to-column : ∀ {n} (M : Mat n) a → TC.adj a ≡ a → gram M ≈ scale a identity → columnGram M ≈ scale a identity
row-to-column M a ha h i j = trans (column-product M i j)
  (trans (solve 2 (λ c s → c := (c :- s) :+ s) refl (product M i j) (scale a identity i j))
    (trans (cong (_+ scale a identity i j) (zero-trace-gram (residual M a) (residual-trace-zero M a ha h) i j))
      (+-identityˡ (scale a identity i j))))

column-from-row : ∀ {d} (M : Mat d) n → gram M ≈ scale (twoPower n) identity → columnGram M ≈ scale (twoPower n) identity
column-from-row M n = row-to-column M (twoPower n) (twoPower-real n)
