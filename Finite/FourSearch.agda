{-# OPTIONS --safe --without-K #-}

-- Four-row search correctness is proved before instantiating large alphabets.
module Finite.FourSearch where

open import Finite.Enumeration using (concatMap-member)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F)
open import Data.Fin using (Fin; _≟_)
open import Data.Vec.Base as V using (Vec; []; _∷_; lookup)
open import Data.List.Base as L using (List; map; concatMap; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-concatMap⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

any-witness : ∀ {A : Set} {Q : A → Set} {xs} → Any Q xs → Σ[ x ∈ A ] (x ∈ xs) × Q x
any-witness (here h) = _ , here refl , h
any-witness (there h) with any-witness h
... | x , hx , hq = x , there hx , hq

bind-witness : ∀ {A B : Set} (f : A → List B) {xs y} → y ∈ concatMap f xs →
  Σ[ x ∈ A ] (x ∈ xs) × (y ∈ f x)
bind-witness f h = any-witness (∈-concatMap⁻ f h)

module Search {A : Set}
  (compatible : A → A → Set) (compatible? : ∀ a b → Dec (compatible a b))
  (valid : Vec A 4 → Set) (valid? : ∀ M → Dec (valid M))
  (firsts others : List A) where

  quad : A → A → A → A → Vec A 4
  quad a b c d = a ∷ b ∷ c ∷ d ∷ []

  record Conditions (M : Vec A 4) : Set where
    field
      first : lookup M 0F ∈ firsts
      second : lookup M 1F ∈ others
      third : lookup M 2F ∈ others
      fourth : lookup M 3F ∈ others
      orth01 : compatible (lookup M 0F) (lookup M 1F)
      orth02 : compatible (lookup M 0F) (lookup M 2F)
      orth03 : compatible (lookup M 0F) (lookup M 3F)
      orth12 : compatible (lookup M 1F) (lookup M 2F)
      orth13 : compatible (lookup M 1F) (lookup M 3F)
      orth23 : compatible (lookup M 2F) (lookup M 3F)
      final : valid M

  compatibleRows : List A → A → List A
  compatibleRows rs r = filter (compatible? r) rs

  filter-complete : ∀ rs r s → s ∈ rs → compatible r s → s ∈ compatibleRows rs r
  filter-complete rs r s hs ho = ∈-filter⁺ (compatible? r) hs ho

  filter-sound : ∀ rs r s → s ∈ compatibleRows rs r → (s ∈ rs) × compatible r s
  filter-sound rs r s = ∈-filter⁻ (compatible? r) {v = s} {xs = rs}

  afterOne : A → List A
  afterOne a = compatibleRows others a
  afterTwo : A → A → List A
  afterTwo a b = compatibleRows (afterOne a) b
  afterThree : A → A → A → List A
  afterThree a b c = compatibleRows (afterTwo a b) c

  lastRows : A → A → A → List A
  lastRows a b c = filter (λ d → valid? (quad a b c d)) (afterThree a b c)

  thirdTail : A → A → A → List (Vec A 4)
  thirdTail a b c = map (quad a b c) (lastRows a b c)
  secondTail : A → A → List (Vec A 4)
  secondTail a b = concatMap (thirdTail a b) (afterTwo a b)
  firstTail : A → List (Vec A 4)
  firstTail a = concatMap (secondTail a) (afterOne a)
  enumerate : List (Vec A 4)
  enumerate = concatMap firstTail firsts

  complete : ∀ M → Conditions M → M ∈ enumerate
  complete (a ∷ b ∷ c ∷ d ∷ []) h = concatMap-member firstTail (first h)
    (concatMap-member (secondTail a) hb (concatMap-member (thirdTail a b) hc
      (∈-map⁺ (quad a b c) (∈-filter⁺ (λ d → valid? (quad a b c d)) hd (final h)))))
    where
    open Conditions
    hb : b ∈ afterOne a
    hb = filter-complete others a b (second h) (orth01 h)
    hc : c ∈ afterTwo a b
    hc = filter-complete (afterOne a) b c (filter-complete others a c (third h) (orth02 h)) (orth12 h)
    hd : d ∈ afterThree a b c
    hd = filter-complete (afterTwo a b) c d
      (filter-complete (afterOne a) b d (filter-complete others a d (fourth h) (orth03 h)) (orth13 h)) (orth23 h)

  sound : ∀ M → M ∈ enumerate → Conditions M
  sound M h with bind-witness firstTail {xs = firsts} h
  ... | a , ha , h1 with bind-witness (secondTail a) {xs = afterOne a} h1
  ... | b , hb , h2 with bind-witness (thirdTail a b) {xs = afterTwo a b} h2
  ... | c , hc , h3 with ∈-map⁻ (quad a b c) {xs = lastRows a b c} h3
  ... | d , hd , refl = record
    { first = ha; second = proj₁ b1; third = proj₁ c1; fourth = proj₁ d1
    ; orth01 = proj₂ b1; orth02 = proj₂ c1; orth03 = proj₂ d1
    ; orth12 = proj₂ c2; orth13 = proj₂ d2; orth23 = proj₂ d3; final = proj₂ df }
    where
    b1 = filter-sound others a b hb
    c2 = filter-sound (afterOne a) b c hc
    c1 = filter-sound others a c (proj₁ c2)
    df = ∈-filter⁻ (λ d → valid? (quad a b c d)) {v = d} {xs = afterThree a b c} hd
    d3 = filter-sound (afterTwo a b) c d (proj₁ df)
    d2 = filter-sound (afterOne a) b d (proj₁ d3)
    d1 = filter-sound others a d (proj₁ d2)

  module Partition {size} (tag : A → Fin size) where

    branches : A → Fin size → List (Vec A 4)
    branches a t = concatMap (secondTail a) (filter (λ b → tag b ≟ t) (afterOne a))

    partition-complete : ∀ a b c d → Conditions (quad a b c d) → quad a b c d ∈ branches a (tag b)
    partition-complete a b c d h = concatMap-member (secondTail a)
      (∈-filter⁺ (λ x → tag x ≟ tag b) hb refl)
      (concatMap-member (thirdTail a b) hc
        (∈-map⁺ (quad a b c) (∈-filter⁺ (λ d → valid? (quad a b c d)) hd (final h))))
      where
      open Conditions
      hb : b ∈ afterOne a
      hb = filter-complete others a b (second h) (orth01 h)
      hc : c ∈ afterTwo a b
      hc = filter-complete (afterOne a) b c (filter-complete others a c (third h) (orth02 h)) (orth12 h)
      hd : d ∈ afterThree a b c
      hd = filter-complete (afterTwo a b) c d
        (filter-complete (afterOne a) b d (filter-complete others a d (fourth h) (orth03 h)) (orth13 h)) (orth23 h)
