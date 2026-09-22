-- This module is an Agda port of the module Quantum.Synthesis.StepComp
-- of the Haskell package newsynth (by N. J. Ross and P. Selinger).
--
-- It provides step computations. These are computations that can be
-- run, stopped, resumed, parallelized, and/or bounded in runtime.
--
-- The Haskell type
--
--   data StepComp a = Done a | Tick (StepComp a)
--
-- is lazy, so it contains infinite computations such as "diverge".
-- In Agda, StepComp is a mixed inductive/coinductive type: the
-- argument of Tick is a coinductive ∞StepComp, which is forced with
-- "force". Corecursive definitions are written with copatterns, e.g.
--
--   loop : StepComp A
--   loop = Tick λ where .force -> loop
--
-- Functions that run a computation to completion can only do so for a
-- bounded number of steps: run-bounded returns a Maybe, and run and
-- run-with-steps (which diverge in Haskell on infinite computations)
-- use the large default bound run-fuel.
--
-- The monad operations are provided both as plain functions (_>>=_,
-- _>>_, return, pure, fmap, _<$>_, _<*>_), which make Agda's
-- do-notation work when this module is opened, and as a RawMonad
-- instance of the standard library.

{-# OPTIONS --without-K --safe --guardedness #-}

module Quantum.Synthesis.StepComp where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _∸_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.String.Base using (_++_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Effect.Monad using (RawMonad ; mkRawMonad)

open import Instances
open import Literals

private
  variable
    A B : Set

-- ----------------------------------------------------------------------
-- * A monad for step computations

-- A step computation can be run for a specified number of steps,
-- stopped, continued, and interleaved. Such a computation produces
-- "ticks" at user-defined intervals, which must be consumed by the
-- environment for the computation to continue.
data StepComp (A : Set) : Set

-- A delayed step computation.
record ∞StepComp (A : Set) : Set where
  coinductive
  field
    force : StepComp A
open ∞StepComp public

data StepComp A where
  -- Terminate with a result.
  Done : A -> StepComp A
  -- Produce a "tick", then resume the computation.
  Tick : ∞StepComp A -> StepComp A

-- Delay a computation (without any further ticks).
delay : StepComp A -> ∞StepComp A
delay c .force = c

-- ----------------------------------------------------------------------
-- ** Monad operations

infixl 1 _>>=_ _>>_
infixl 4 _<$>_ _<*>_

return pure : A -> StepComp A
return a = Done a
pure = return

_>>=_ : StepComp A -> (A -> StepComp B) -> StepComp B
bind∞ : ∞StepComp A -> (A -> StepComp B) -> ∞StepComp B
Done a >>= g = g a
Tick c >>= g = Tick (bind∞ c g)
bind∞ c g .force = c .force >>= g

_>>_ : StepComp A -> StepComp B -> StepComp B
c >> d = c >>= λ _ -> d

fmap _<$>_ : (A -> B) -> StepComp A -> StepComp B
fmap f c = c >>= λ a -> return (f a)
_<$>_ = fmap

_<*>_ : StepComp (A -> B) -> StepComp A -> StepComp B
cf <*> ca = cf >>= λ f -> ca >>= λ a -> return (f a)

instance
  MonadStepComp : RawMonad StepComp
  MonadStepComp = mkRawMonad StepComp return _>>=_

-- Printing, as in newsynth: "Done(...)" or "Incomplete".
instance
  ShowStepComp : {{_ : Show A}} -> Show (StepComp A)
  ShowStepComp .showsPrec _ (Done a) = "Done(" ++ show a ++ ")"
  ShowStepComp .showsPrec _ (Tick _) = "Incomplete"

-- ----------------------------------------------------------------------
-- * Basic operations

-- Issue a single tick.
tick : StepComp ⊤
tick = Tick (delay (Done tt))

-- Run the step computation for one step.
untick : StepComp A -> StepComp A
untick (Done a) = Done a
untick (Tick c) = c .force

-- Fast-forward a computation by n steps. This is essentially
-- equivalent to doing n 'untick' operations.
forward : ℕ -> StepComp A -> StepComp A
forward zero c = c
forward (suc n) (Done a) = Done a
forward (suc n) (Tick c) = forward n (c .force)

-- Check whether a step computation is completed.
is-done : StepComp A -> Bool
is-done (Done a) = true
is-done (Tick c) = false

-- Retrieve the result of a completed step computation (or nothing if
-- it is incomplete).
get-result : StepComp A -> Maybe A
get-result (Done a) = just a
get-result (Tick c) = nothing

-- Run a subsidiary computation for up to n steps, translated into an
-- equal number of steps of the parent computation.
subtask : ℕ -> StepComp A -> StepComp (StepComp A)
subtask zero c = Done c
subtask (suc n) (Done a) = Done (Done a)
subtask (suc n) (Tick c) = Tick λ where .force -> subtask n (c .force)

-- Run a subtask, speeding it up by a factor of n ≥ 1. Every 1 tick of
-- the calling task corresponds to up to n ticks of the subtask. (For
-- n = 0, this behaves like n = 1.)
speedup : ℕ -> StepComp A -> StepComp A
speedup n (Done a) = Done a
speedup n (Tick c) = Tick λ where .force -> speedup n (forward (n ∸ 1) (c .force))

-- Run two step computations in parallel, until one branch terminates.
-- Tick allocation is associative: each tick of the parent function
-- translates into one tick for each subcomputation. Therefore, when
-- running, e.g., three subcomputations in parallel, they will each
-- receive an approximately equal number of ticks.
parallel : StepComp A -> StepComp B -> StepComp ((A × StepComp B) ⊎ (StepComp A × B))
parallel (Done a) c = Done (inj₁ (a , c))
parallel c@(Tick _) (Done b) = Done (inj₂ (c , b))
parallel (Tick c) (Tick c') = Tick λ where .force -> parallel (c .force) (c' .force)

-- Wrap a step computation to return the number of steps, in addition
-- to the result.
with-counter : StepComp A -> StepComp (A × ℕ)
with-counter c = aux 0 c
  where
    aux : {A : Set} -> ℕ -> StepComp A -> StepComp (A × ℕ)
    aux n (Done a) = Done (a , n)
    aux n (Tick c) = Tick λ where .force -> aux (suc n) (c .force)

-- ----------------------------------------------------------------------
-- ** Run functions

-- Run a step computation for at most n steps.
run-bounded : ℕ -> StepComp A -> Maybe A
run-bounded n c = get-result (forward n c)

-- The number of steps after which run and run-with-steps give up
-- (10¹²; at a rate of 10⁹ ticks per second, this takes about 17
-- minutes).
run-fuel : ℕ
run-fuel = 1000000000000

-- Run a step computation until it finishes. Unlike Haskell (where
-- run diverges on non-terminating computations), this gives up after
-- run-fuel steps and returns nothing.
run : StepComp A -> Maybe A
run = run-bounded run-fuel

-- Run a step computation until it finishes, and also return the
-- number of steps it took. Gives up after run-fuel steps.
run-with-steps : StepComp A -> Maybe (A × ℕ)
run-with-steps c = run (with-counter c)

-- ----------------------------------------------------------------------
-- * Other operations

-- Do nothing, forever.
diverge : StepComp A
diverge = Tick λ where .force -> diverge

-- Run two step computations in parallel. The first one to complete
-- becomes the result of the computation.
parallel-first : StepComp A -> StepComp A -> StepComp A
parallel-first c1 c2 = parallel c1 c2 >>= λ where
  (inj₁ (a , _)) -> return a
  (inj₂ (_ , a)) -> return a

-- Run two step computations in parallel. If either computation
-- returns nothing, return nothing. Otherwise, return the pair of
-- results.
parallel-maybe : StepComp (Maybe A) -> StepComp (Maybe B) -> StepComp (Maybe (A × B))
parallel-maybe c1 c2 = parallel c1 c2 >>= λ where
  (inj₁ (nothing , _)) -> return nothing
  (inj₂ (_ , nothing)) -> return nothing
  (inj₁ (just a , c2)) -> c2 >>= λ where
    nothing -> return nothing
    (just b) -> return (just (a , b))
  (inj₂ (c1 , just b)) -> c1 >>= λ where
    nothing -> return nothing
    (just a) -> return (just (a , b))

-- Run a list of step computations in parallel. If any computation
-- returns nothing, return nothing. Otherwise, return the list of
-- results.
parallel-list-maybe : List (StepComp (Maybe A)) -> StepComp (Maybe (List A))
parallel-list-maybe [] = return (just [])
parallel-list-maybe (h ∷ t) = parallel-maybe h (parallel-list-maybe t) >>= λ where
  nothing -> return nothing
  (just (h' , t')) -> return (just (h' ∷ t'))
