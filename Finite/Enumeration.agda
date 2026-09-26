{-# OPTIONS --safe --without-K #-}

-- Generic finite search completeness. Predicate filtering changes the
-- amount of computation, never the set of permitted candidates.
module Finite.Enumeration where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List.Base as L using (List; []; _∷_; concatMap; map; allFin)
open import Data.Vec.Base as V using (Vec; []; _∷_; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin; ∈-concatMap⁺; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; subst)

decExists : ∀ n (P : Fin n → Set) → (∀ i → Dec (P i)) → Dec (Σ[ i ∈ Fin n ] P i)
decExists zero P d = no (λ { (() , _) })
decExists (suc n) P d with d Data.Fin.zero
... | yes p = yes (Data.Fin.zero , p)
... | no np with decExists n (λ i → P (Data.Fin.suc i)) (λ i → d (Data.Fin.suc i))
...   | yes (i , pi) = yes (Data.Fin.suc i , pi)
...   | no nps = no (λ { (Data.Fin.zero , p) → np p ; (Data.Fin.suc i , p) → nps (i , p) })

listAll : ∀ {A : Set} → (A → Bool) → List A → Bool
listAll f [] = true
listAll f (x ∷ xs) = f x ∧ listAll f xs

listAll-sound : ∀ {A : Set} (f : A → Bool) xs → listAll f xs ≡ true → ∀ {x} → x ∈ xs → f x ≡ true
listAll-sound f (y ∷ ys) h (here refl) with f y
... | true = refl
... | false = ⊥-elim (bad h) where bad : false ≡ true → Data.Empty.⊥; bad ()
listAll-sound f (y ∷ ys) h (there hx) with f y
... | true = listAll-sound f ys h hx
... | false = ⊥-elim (bad h) where bad : false ≡ true → Data.Empty.⊥; bad ()

concatMap-member : ∀ {A B : Set} (f : A → List B) {xs x y} → x ∈ xs → y ∈ f x → y ∈ concatMap f xs
concatMap-member f hx hy = ∈-concatMap⁺ f (Any.map (λ eq → subst (λ z → _ ∈ f z) eq hy) hx)

module Search {size : ℕ} (compatible : Fin size → Fin size → Bool) where

  select : ∀ {A : Set} → Bool → List A → List A
  select false xs = []
  select true xs = xs

  select-member : ∀ {A : Set} b (xs : List A) {x} → b ≡ true → x ∈ xs → x ∈ select b xs
  select-member true xs eq member = member
  select-member false xs () member

  enumerate : ∀ n → (Fin size → Bool) → List (Vec (Fin size) n)
  enumerate zero allowed = [] ∷ []
  enumerate (suc n) allowed = concatMap
    (λ a → select (allowed a) (map (V._∷_ a) (enumerate n (λ b → allowed b ∧ compatible a b)))) (allFin size)

  enumerate-complete : ∀ n allowed (v : Vec (Fin size) n) →
    (∀ i → allowed (lookup v i) ≡ true) →
    (∀ i j → compatible (lookup v i) (lookup v j) ≡ true) → v ∈ enumerate n allowed
  enumerate-complete zero allowed [] ha hp = here refl
  enumerate-complete (suc n) allowed (a ∷ tail) ha hp = concatMap-member
    (λ a → select (allowed a) (map (V._∷_ a) (enumerate n (λ b → allowed b ∧ compatible a b))))
    (∈-allFin a) (select-member (allowed a) _ (ha Data.Fin.zero) member)
    where
    tailAllowed : ∀ i → (allowed (lookup tail i) ∧ compatible a (lookup tail i)) ≡ true
    tailAllowed i = cong₂ _∧_ (ha (Data.Fin.suc i)) (hp Data.Fin.zero (Data.Fin.suc i))
    tailPairs : ∀ i j → compatible (lookup tail i) (lookup tail j) ≡ true
    tailPairs i j = hp (Data.Fin.suc i) (Data.Fin.suc j)
    member = ∈-map⁺ (V._∷_ a) (enumerate-complete n (λ b → allowed b ∧ compatible a b) tail tailAllowed tailPairs)

  enumerate-tail-complete : ∀ n a (v : Vec (Fin size) n) →
    (∀ i → compatible a (lookup v i) ≡ true) →
    (∀ i j → compatible (lookup v i) (lookup v j) ≡ true) →
    (a V.∷ v) ∈ map (V._∷_ a) (enumerate n (compatible a))
  enumerate-tail-complete n a v ha hp = ∈-map⁺ (V._∷_ a) (enumerate-complete n (compatible a) v ha hp)
