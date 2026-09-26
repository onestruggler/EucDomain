{-# OPTIONS --safe --without-K #-}

-- Complete finite search with pruning by a predicate on partial prefixes.
module Finite.PrefixSearch where

open import Finite.Enumeration using (concatMap-member; listAll)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_; _++_; [_]; length; concatMap; allFin)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong₂)

all-true : ∀ {A : Set} (f : A → Bool) xs → (∀ {x} → x ∈ xs → f x ≡ true) → listAll f xs ≡ true
all-true f [] h = refl
all-true f (x ∷ xs) h = cong₂ _∧_ (h (here refl)) (all-true f xs (λ hx → h (there hx)))

keep : ∀ {A : Set} → Bool → List A → List A
keep true xs = xs
keep false xs = []

keep-member : ∀ {A : Set} b (xs : List A) {x} → b ≡ true → x ∈ xs → x ∈ keep b xs
keep-member true xs h hx = hx
keep-member false xs () hx

module Search {size : ℕ} (good : List (Fin size) → Bool) where

  enumerate : ℕ → List (Fin size) → List (List (Fin size))
  enumerate zero prefix = [ prefix ]
  enumerate (suc n) prefix = concatMap (λ a →
    keep (good (prefix ++ [ a ])) (enumerate n (prefix ++ [ a ]))) (allFin size)

  PrefixClosed : List (Fin size) → Set
  PrefixClosed xs = ∀ prefix suffix → prefix ++ suffix ≡ xs → good prefix ≡ true

  complete : ∀ prefix suffix → PrefixClosed (prefix ++ suffix) →
    prefix ++ suffix ∈ enumerate (length suffix) prefix
  complete prefix [] h = subst (_∈ enumerate zero prefix) (sym (++-identityʳ prefix)) (here refl)
  complete prefix (a ∷ suffix) h = subst (_∈ enumerate (suc (length suffix)) prefix)
    (++-assoc prefix [ a ] suffix)
    (concatMap-member (λ a → keep (good (prefix ++ [ a ])) (enumerate (length suffix) (prefix ++ [ a ])))
      (∈-allFin a) (keep-member (good (prefix ++ [ a ])) _
        (h (prefix ++ [ a ]) suffix (++-assoc prefix [ a ] suffix))
        (complete (prefix ++ [ a ]) suffix closed)))
    where
    closed : PrefixClosed ((prefix ++ [ a ]) ++ suffix)
    closed p s hp = h p s (trans hp (++-assoc prefix [ a ] suffix))
