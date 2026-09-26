{-# OPTIONS --safe --without-K #-}

-- Generic facts keep search proofs independent of expensive matrix decisions.
module Finite.BooleanSearch where
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

and-complete : ∀ {P Q : Set} (p : Dec P) (q : Dec Q) → P → Q → does p ∧ does q ≡ true
and-complete (yes _) (yes _) hp hq = refl
and-complete (no np) _ hp hq = ⊥-elim (np hp)
and-complete (yes _) (no nq) hp hq = ⊥-elim (nq hq)

and-sound : ∀ {P Q : Set} (p : Dec P) (q : Dec Q) → does p ∧ does q ≡ true → P × Q
and-sound (yes hp) (yes hq) h = hp , hq
and-sound (no _) _ ()
and-sound (yes _) (no _) ()

find : ∀ {A : Set} → (A → Bool) → List A → Maybe A
find p [] = nothing
find p (x ∷ xs) = if p x then just x else find p xs

member-complete : ∀ {A : Set} (p : A → Bool) xs x → x ∈ xs → p x ≡ true →
  Σ[ y ∈ A ] find p xs ≡ just y
member-complete p (x ∷ xs) .x (here refl) h rewrite h = x , refl
member-complete p (y ∷ xs) x (there member) h with p y
... | true = y , refl
... | false = member-complete p xs x member h

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

sound : ∀ {A : Set} (p : A → Bool) xs y → find p xs ≡ just y → (y ∈ xs) × (p y ≡ true)
sound p [] y ()
sound p (x ∷ xs) y h with p x in hp
... | true = subst (λ z → (z ∈ (x ∷ xs)) × (p z ≡ true)) (just-injective h) (here refl , hp)
... | false = there (proj₁ tail) , proj₂ tail
  where tail = sound p xs y h
