{-# OPTIONS --safe --without-K #-}

-- The search commits to the first eligible suffix, including inner failure.
module Finite.SuffixSearch where
open import Data.Bool using (if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

map-witness : ∀ {X Y : Set} (f : X → Y) m y → map f m ≡ just y →
  Σ[ x ∈ X ] (m ≡ just x) × (y ≡ f x)
map-witness f nothing y ()
map-witness f (just x) y h = x , refl , sym (just-injective h)

module Traversal {S R O : Set} (P Q : S → Set)
  (p : ∀ s → Dec (P s)) (q : ∀ s → Dec (Q s))
  (inner : S → Maybe R) (join : S → R → O)
  (search : List S → Maybe O)
  (empty : search [] ≡ nothing)
  (cons : ∀ s ss → search (s ∷ ss) ≡
    (if does (p s) then
      (if does (q s) then map (join s) (inner s) else search ss)
     else search ss)) where

  Eligible : S → Set
  Eligible s = P s × Q s

  LookupTotal : List S → Set
  LookupTotal ss = ∀ s → s ∈ ss → Eligible s → Σ[ r ∈ R ] inner s ≡ just r

  skip-head : ∀ s ss t → t ∈ (s ∷ ss) → Eligible t → (Eligible s → ⊥) → t ∈ ss
  skip-head s ss .s (here refl) e reject = ⊥-elim (reject e)
  skip-head s ss t (there member) e reject = member

  complete : ∀ ss → LookupTotal ss → ∀ s → s ∈ ss → Eligible s →
    Σ[ out ∈ O ] search ss ≡ just out
  complete [] total s () eligible
  complete (t ∷ ts) total s member eligible rewrite cons t ts with p t | q t
  ... | yes hp | yes hq = finish (total t (here refl) (hp , hq))
    where
    finish : (Σ[ r ∈ R ] inner t ≡ just r) → Σ[ out ∈ O ] map (join t) (inner t) ≡ just out
    finish (r , h) = join t r , cong (map (join t)) h
  ... | yes hp | no nq = complete ts (λ c hm → total c (there hm)) s
    (skip-head t ts s member eligible (λ e → nq (proj₂ e))) eligible
  ... | no np | _ = complete ts (λ c hm → total c (there hm)) s
    (skip-head t ts s member eligible (λ e → np (proj₁ e))) eligible

  record Selected (ss : List S) (out : O) : Set where
    field
      suffix : S
      prefix : R
      member : suffix ∈ ss
      eligible : Eligible suffix
      found : inner suffix ≡ just prefix
      output : out ≡ join suffix prefix

  sound : ∀ ss out → search ss ≡ just out → Selected ss out
  sound [] out h with trans (sym empty) h
  ... | ()
  sound (s ∷ ss) out h with p s | q s | trans (sym (cons s ss)) h
  ... | yes hp | yes hq | hit = finish (map-witness (join s) (inner s) out hit)
    where
    finish : (Σ[ r ∈ R ] (inner s ≡ just r) × (out ≡ join s r)) → Selected (s ∷ ss) out
    finish (r , found , output) = record
      { suffix = s; prefix = r; member = here refl; eligible = hp , hq
      ; found = found; output = output }
  ... | yes hp | no nq | tail = record
    { suffix = Selected.suffix selected; prefix = Selected.prefix selected
    ; member = there (Selected.member selected); eligible = Selected.eligible selected
    ; found = Selected.found selected; output = Selected.output selected }
    where selected = sound ss out tail
  ... | no np | _ | tail = record
    { suffix = Selected.suffix selected; prefix = Selected.prefix selected
    ; member = there (Selected.member selected); eligible = Selected.eligible selected
    ; found = Selected.found selected; output = Selected.output selected }
    where selected = sound ss out tail
