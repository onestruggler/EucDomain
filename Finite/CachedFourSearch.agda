{-# OPTIONS --safe --without-K #-}
module Finite.CachedFourSearch where
import Finite.FourSearch as Four
open import Data.Fin using (Fin; _≟_)
open import Data.Vec.Base using (Vec)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; filter)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong₂)

spine : ∀ {A B : Set} → List A → (List A → B) → B
spine [] f = f []
spine (x ∷ xs) f = spine xs (λ ys → f (x ∷ ys))

spine-id : ∀ {A B : Set} (xs : List A) (f : List A → B) → spine xs f ≡ f xs
spine-id [] f = refl
spine-id (x ∷ xs) f = spine-id xs (λ ys → f (x ∷ ys))

concat-cong : ∀ {A B : Set} (f g : A → List B) xs → (∀ x → f x ≡ g x) → concatMap f xs ≡ concatMap g xs
concat-cong f g [] h = refl
concat-cong f g (x ∷ xs) h = cong₂ _++_ (h x) (concat-cong f g xs h)

module Search {A : Set}
  (compatible : A → A → Set) (compatible? : ∀ a b → Dec (compatible a b))
  (valid : Vec A 4 → Set) (valid? : ∀ M → Dec (valid M))
  (firsts others : List A) where
  module Plain = Four.Search compatible compatible? valid valid? firsts others
  open Plain using (quad; compatibleRows; afterOne; afterTwo)

  second : A → A → List A → List (Vec A 4)
  second a b rows = spine (compatibleRows rows b) λ rest →
    concatMap (λ c → map (quad a b c)
      (filter (λ d → valid? (quad a b c d)) (compatibleRows rest c))) rest

  second-correct : ∀ a b → second a b (afterOne a) ≡ Plain.secondTail a b
  second-correct a b = spine-id (afterTwo a b) (λ rest →
    concatMap (λ c → map (quad a b c)
      (filter (λ d → valid? (quad a b c d)) (compatibleRows rest c))) rest)

  module Partition {size} (tag : A → Fin size) where
    branches : A → Fin size → List (Vec A 4)
    branches a t = spine (afterOne a) λ rows →
      concatMap (λ b → second a b rows) (filter (λ b → tag b ≟ t) rows)

    branches-correct : ∀ a t → branches a t ≡ Plain.Partition.branches tag a t
    branches-correct a t = trans (spine-id (afterOne a) (λ rows →
      concatMap (λ b → second a b rows) (filter (λ b → tag b ≟ t) rows)))
      (concat-cong (λ b → second a b (afterOne a)) (Plain.secondTail a)
        (filter (λ b → tag b ≟ t) (afterOne a)) (second-correct a))
