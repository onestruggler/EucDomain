{-# OPTIONS --safe --without-K #-}
module Finite.FourSearchFirst where
import Finite.FourSearch as Four
open import Finite.Enumeration using (concatMap-member)
open import Data.List.Base using (List)
open import Data.Vec.Base using (Vec)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-filter⁺)
open import Relation.Nullary using (Dec)

module First {A : Set}
  (compatible : A → A → Set) (compatible? : ∀ a b → Dec (compatible a b))
  (valid : Vec A 4 → Set) (valid? : ∀ M → Dec (valid M)) (firsts others : List A) where
  module Run = Four.Search compatible compatible? valid valid? firsts others

  complete : ∀ a b c d → Run.Conditions (Run.quad a b c d) → Run.quad a b c d ∈ Run.firstTail a
  complete a b c d h = concatMap-member (Run.secondTail a) hb
    (concatMap-member (Run.thirdTail a b) hc
      (∈-map⁺ (Run.quad a b c) (∈-filter⁺ (λ d → valid? (Run.quad a b c d)) hd (Run.Conditions.final h))))
    where
    open Run.Conditions h
    hb = Run.filter-complete others a b second orth01
    hc = Run.filter-complete (Run.afterOne a) b c (Run.filter-complete others a c third orth02) orth12
    hd = Run.filter-complete (Run.afterTwo a b) c d
      (Run.filter-complete (Run.afterOne a) b d (Run.filter-complete others a d fourth orth03) orth13) orth23
