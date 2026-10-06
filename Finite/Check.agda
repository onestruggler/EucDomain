{-# OPTIONS --safe --without-K #-}

-- Exhaustive checks return ordinary Agda proof terms, not native axioms.
module Finite.Check where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec; yes; no; does)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_)

AllFin : ∀ n → (Fin n → Set) → Set
AllFin zero P = ⊤
AllFin (suc n) P = P zero × AllFin n (λ i → P (suc i))

allFin : ∀ n (P : Fin n → Set) → (∀ i → Dec (P i)) → Dec (AllFin n P)
allFin zero P d = yes tt
allFin (suc n) P d with d zero | allFin n (λ i → P (suc i)) (λ i → d (suc i))
... | yes p | yes ps = yes (p , ps)
... | no np | _ = no (λ h → np (proj₁ h))
... | _ | no nps = no (λ h → nps (proj₂ h))

lookupAll : ∀ {n P} → AllFin n P → ∀ i → P i
lookupAll {suc n} (p , ps) zero = p
lookupAll {suc n} (p , ps) (suc i) = lookupAll ps i

tabulateAll : ∀ {n P} → (∀ i → P i) → AllFin n P
tabulateAll {zero} h = tt
tabulateAll {suc n} h = h zero , tabulateAll (λ i → h (suc i))

checkFin : ∀ n (P : Fin n → Set) (d : ∀ i → Dec (P i)) → True (allFin n P d) → ∀ i → P i
checkFin n P d h = lookupAll (toWitness h)

-- The same checks from `refl : does d ≡ true`. Agda 2.8 checks this several
-- times faster than `tt : True d`, as it only evaluates the decision's Boolean.
decided : ∀ {P : Set} (d : Dec P) → does d ≡ true → P
decided (yes p) _ = p
decided (no _) ()

decideFin : ∀ n (P : Fin n → Set) (d : ∀ i → Dec (P i)) → does (allFin n P d) ≡ true → ∀ i → P i
decideFin n P d h = lookupAll (decided (allFin n P d) h)

decAll : ∀ n (P : Fin n → Set) → (∀ i → Dec (P i)) → Dec (∀ i → P i)
decAll n P d with allFin n P d
... | yes h = yes (lookupAll h)
... | no h = no (λ f → h (tabulateAll f))

decImplies : ∀ {P Q : Set} → Dec P → Dec Q → Dec (P → Q)
decImplies (no np) _ = yes (λ p → ⊥-elim (np p))
decImplies (yes p) (yes q) = yes (λ _ → q)
decImplies (yes p) (no nq) = no (λ h → nq (h p))
