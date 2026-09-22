-- Tests for Quantum.Synthesis.StepComp, checked by evaluation.

{-# OPTIONS --without-K --safe --guardedness #-}

module Test.StepComp where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Bool.Base using (true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (⊤ ; tt)

open import Instances
open import Literals
open import Quantum.Synthesis.StepComp

-- A computation that takes k steps and returns x.
after : {A : Set} -> ℕ -> A -> StepComp A
after ℕ.zero x = return x
after (ℕ.suc k) x = do
  tick
  after k x

count : ℕ -> ℕ -> StepComp ℕ
count = after

c5 : StepComp ℕ
c5 = count 5 5

_ : run-with-steps c5 ≡ just (5 , 5)
_ = refl

_ : run-bounded 4 c5 ≡ nothing
_ = refl

_ : run-bounded 5 c5 ≡ just 5
_ = refl

_ : is-done (forward 4 c5) ≡ false
_ = refl

_ : get-result (untick (forward 4 c5)) ≡ just 5
_ = refl

_ : run-with-steps (speedup 2 c5) ≡ just (5 , 3)
_ = refl

_ : run-with-steps (speedup 10 c5) ≡ just (5 , 1)
_ = refl

-- subtask 3 runs 3 steps, and returns the rest of the computation.
_ : run-with-steps (subtask 3 c5 >>= λ c -> return (run-with-steps c)) ≡ just (just (5 , 2) , 3)
_ = refl

_ : run-bounded 1000 (diverge {ℕ}) ≡ nothing
_ = refl

_ : run-with-steps (parallel-first diverge c5) ≡ just (5 , 5)
_ = refl

_ : run-with-steps (parallel-first (count 3 3) c5) ≡ just (3 , 3)
_ = refl

_ : run-with-steps (parallel-maybe (fmap just (count 2 2)) (fmap just c5)) ≡ just (just (2 , 5) , 5)
_ = refl

_ : run-with-steps (parallel-maybe (after 7 (nothing {A = ℕ})) (fmap just c5)) ≡ just (nothing , 7)
_ = refl

-- A computation returning nothing stops the others early.
_ : run-with-steps (parallel-list-maybe (fmap just c5 ∷ after 2 nothing ∷ diverge ∷ []))
    ≡ just (nothing , 2)
_ = refl

_ : run-with-steps (parallel-list-maybe (fmap just c5 ∷ fmap just (count 2 2) ∷ fmap just (count 7 7) ∷ []))
    ≡ just (just (5 ∷ 2 ∷ 7 ∷ []) , 7)
_ = refl

_ : show c5 ≡ "Incomplete"
_ = refl

_ : show (forward 5 c5) ≡ "Done(5)"
_ = refl

_ : run-with-steps ((λ x y -> x + y) <$> c5 <*> count 2 10) ≡ just (15 , 7)
_ = refl
