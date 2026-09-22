-- This module is an Agda port of the module
-- Quantum.Synthesis.Diophantine of the Haskell package newsynth (by
-- N. J. Ross and P. Selinger).
--
-- It provides some number-theoretic functions, particularly functions
-- for solving the Diophantine equation
--
--   t† t = ξ,
--
-- where ξ ∈ ℤ[√2] and t ∈ ℤ[ω], or ξ ∈ 𝔻[√2] and t ∈ 𝔻[ω].
--
-- In general, solving this equation can be hard, as it depends on the
-- ability to factor the integer n = ξ• ξ into primes. We formulate
-- the solution as a step computation (see Quantum.Synthesis.StepComp),
-- so that the caller can dynamically determine how much time to spend
-- on solving the equation, or can attempt to solve several such
-- equations in parallel.
--
-- In many cases, even a partial factorization of n is sufficient to
-- determine that no solution exists. This implementation is written
-- to take advantage of such cases.
--
-- Differences from the Haskell implementation:
--
--  * Integer div/mod/gcd are Haskell's (see _div_, _mod_, gcd in
--    Quantum.Synthesis.EuclideanDomain).
--    Euclidean-domain computations on ℤ use DMℤ, which agrees with
--    Haskell's divMod on the positive numbers occurring here.
--  * Haskell's "assert"s are omitted (they are disabled in newsynth's
--    optimized builds anyway).
--  * The internal functions dioph-int-assoc, dioph-zroottwo-assoc and
--    friends recurse on proper factors of their argument. This
--    recursion is bounded by an explicit fuel argument (the functions
--    with a prime, e.g. dioph-int-assoc', take the fuel; the ones
--    without compute a sufficient fuel, the bit length of the norm).
--    If the fuel ran out (which cannot happen), the computation
--    diverges.
--  * The interleaving of the prime solver and the factoring solver in
--    dioph-int-assoc and dioph-zroottwo-assoc is written as an
--    explicit state machine (interleave), in order to make the
--    corecursion syntactically guarded; it has exactly the same
--    step behavior as the Haskell code.
--  * Exponents (multiplicities, step counts) are natural numbers.
--  * power-mod with a negative exponent returns 1 (Haskell: loops).
--  * Results (including step counts) agree exactly with newsynth for
--    the same StdGen (see Test.DiophantineRun).
--  * Usage caveat: do not use "with" on these step computations in
--    code that is type-checked with concrete arguments (e.g.
--    "f x with run (diophantine g x)"); the with-abstraction
--    normalizes the whole computation, which explodes. Pattern match
--    in a helper function instead.
--  * In root-mod, the condition "a mod n == -1" is never true for
--    n > 0 (as in Haskell, where mod binds tighter than ==), so the
--    special case is never taken; this is faithfully preserved.

{-# OPTIONS --without-K --safe --guardedness #-}

module Quantum.Synthesis.Diophantine where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; replicate ; map ; foldr)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])

open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Function.Base using (case_of_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.EuclideanDomain
open import Quantum.Synthesis.StepComp
open import Quantum.Synthesis.Random

-- ----------------------------------------------------------------------
-- * Factoring

-- Given a factorization n = ab of some element of a Euclidean domain,
-- find a factorization of n into relatively prime factors,
--
--   n = u c₁^k₁ ⋯ cₘ^kₘ,
--
-- where m ≥ 2, u is a unit, and c₁, …, cₘ are pairwise relatively
-- prime.
--
-- While this is not quite a prime factorization of n, it can be a
-- useful intermediate step for computations that proceed by recursion
-- on relatively prime factors (such as Euler's φ-function, the
-- solution of Diophantine equations, etc.).
--
-- The main loop is bounded by a (very generous) fuel; if it runs out,
-- the factors found so far are returned.
module _ {A : Set} {{_ : Ring A}} {{_ : DecEq A}} {{_ : DivMod A}} {{_ : Rank A}} where
  open LiteralsFor A

  private
    aux2 : A -> List (A × ℕ) -> A × List A × List (A × ℕ)
    aux2 h [] = 1 , [] , (h , 1) ∷ []
    -- (Intermediate results are passed as function arguments, since
    -- Agda's "let" and "where" do not share them.)
    aux2 h ((f , k) ∷ fs) =
      if euclid-associates h f then (euclid-div h f , [] , (f , suc k) ∷ fs)
      else with-gcd (euclid-gcd h f)
      where
        with-gcd : A -> A × List A × List (A × ℕ)
        with-gcd d =
          if is-unit d then
            (case aux2 h fs of λ where (u , hs , fs') -> (u , hs , (f , k) ∷ fs'))
          else (1 , (euclid-div h d ∷ d ∷ replicate k (euclid-div f d) ++ replicate k d) , fs)

    aux : ℕ -> A -> List A -> List (A × ℕ) -> A × List (A × ℕ)
    aux _ u [] fs = u , fs
    aux zero u (_ ∷ _) fs = u , fs
    aux (suc fuel) u (h ∷ t) fs =
      if is-unit h then aux fuel (h * u) t fs
      else (case aux2 h fs of λ where (u' , hs , fs') -> aux fuel (u' * u) (hs ++ t) fs')

  relatively-prime-factors : A -> A -> A × List (A × ℕ)
  relatively-prime-factors a b = aux fuel 1 (a ∷ b ∷ []) []
    where
      r = rank a + rank b + 8
      fuel = r * r

-- ----------------------------------------------------------------------
-- * Computations in ℤₙ

-- Modular exponentiation, using the method of repeated squaring.
-- power-mod a k n computes aᵏ (mod n).
power-mod : ℤ -> ℤ -> ℤ -> ℤ
power-mod a -[1+ _ ] n = 1
power-mod a (+ k) n = go (suc (hibit k)) k
  where
    go : ℕ -> ℕ -> ℤ
    go _ zero = 1
    go _ (suc zero) = a mod n
    go zero _ = 1
    go (suc fuel) k = step (go fuel (k Nat./ 2))
      where
        -- (Agda's "let" is substituted, not shared, so we pass b as
        -- an argument to share it.)
        step : ℤ -> ℤ
        step b = if evenℕ k then (b * b) mod n else (b * b * a) mod n

-- Auxiliary functions for root-mod. mul-mod n r s performs a
-- multiplication in the ring ℤₙ[t]/(t²+rt+s). The elements at+b are
-- represented as pairs (a,b).
mul-mod : ℤ -> ℤ -> ℤ -> ℤ × ℤ -> ℤ × ℤ -> ℤ × ℤ
mul-mod n r s (a , b) (c , d) = reduce (a * c) (a * d + b * c) (b * d)
  where
    reduce : ℤ -> ℤ -> ℤ -> ℤ × ℤ
    reduce x y z = (y - x * r) mod n , (z - x * s) mod n

-- pow-mod n r s x m takes a power xᵐ in the ring ℤₙ[t]/(t²+rt+s).
-- The elements at+b are represented as pairs (a,b).
pow-mod : ℤ -> ℤ -> ℤ -> ℤ × ℤ -> ℤ -> ℤ × ℤ
pow-mod n r s x (+ m) = go (hibit m * 2 + 2) m
  where
    square : ℤ × ℤ -> ℤ × ℤ
    square y = mul-mod n r s y y

    -- the first argument is fuel: two steps halve m.
    go : ℕ -> ℕ -> ℤ × ℤ
    go _ zero = 0 , 1
    go zero _ = 0 , 1
    go (suc fuel) m@(suc m') =
      if evenℕ m then square (go fuel (m Nat./ 2))
      else mul-mod n r s x (go fuel m')
pow-mod n r s x -[1+ _ ] = 0 , 1

-- Note: the corecursive functions below use "with" instead of
-- if_then_else_ or case_of_, since a corecursive call must not be an
-- argument of another function to be recognized as guarded.
module _ {G : Set} {{_ : RandomGen G}} where

  -- Compute a root of −1 in ℤₙ, where n > 0. If n is a positive prime
  -- satisfying n ≡ 1 (mod 4), this succeeds within an expected number
  -- of 2 ticks. Otherwise, it probably diverges.
  --
  -- As a special case, if this function notices that n is not prime,
  -- then it diverges without doing any additional work.
  root-of-negative-one : G -> ℤ -> StepComp ℤ
  root-of-negative-one-step : G -> ℤ -> StepComp ℤ

  root-of-negative-one g n = Tick λ where .force -> root-of-negative-one-step g n

  root-of-negative-one-step g n with randomR (1 , n - 1) g
  ... | b , g' with power-mod b ((n - 1) div 4) n
  ...   | h with (h * h) mod n == n - 1 | (h * h) mod n /= 1
  ...     | true | _ = return h
  ...     | false | true = diverge
  ...     | false | false = root-of-negative-one g' n

  -- Compute a root of a in ℤₙ, where n > 0. If n is an odd prime and
  -- a is a non-zero square in ℤₙ, then this succeeds in an expected
  -- number of 2 ticks. Otherwise, it probably diverges.
  root-mod : G -> ℤ -> ℤ -> StepComp ℤ
  -- One round of root-mod (without the special case), i.e.,
  -- "tick >> res" in Haskell.
  root-mod-loop : G -> ℤ -> ℤ -> StepComp ℤ
  root-mod-step : G -> ℤ -> ℤ -> ℤ -> G -> StepComp ℤ

  root-mod g n a =
    if a mod n == -1 -- handle this special case more efficiently
    then root-of-negative-one g n
    else root-mod-loop g n a

  root-mod-loop g n a with randomR (0 , n - 1) g
  ... | b , g' = Tick λ where .force -> root-mod-step g n a b g'

  root-mod-step g n a b g'
    with pow-mod n ((2 * b) mod n) (b * b - a mod n) (1 , 0) ((n - 1) div 2)
  ... | c , d with inv-mod n c
  ...   | nothing = root-mod-loop g' n a
  ...   | just c' with ((1 - d) * c' + b) mod n
  ...     | t1 with (t1 * t1 - a) mod n == 0
  ...       | true = return t1
  ...       | false = root-mod-loop g' n a

  -- Given a positive composite integer n, find a non-trivial factor of
  -- n using a simple Pollard-rho method. The expected runtime is
  -- O(√p), where p is the size of the smallest prime factor. If n is
  -- not composite (i.e., if n is prime or 1), this function diverges.
  find-factor : G -> ℤ -> StepComp ℤ
  -- find-factor-start g n = "tick >> aux 2 (f 2)" in Haskell, and
  -- find-factor-aux n a g2 x y = "aux x y".
  find-factor-start : G -> ℤ -> StepComp ℤ
  find-factor-aux : ℤ -> ℤ -> G -> ℤ -> ℤ -> StepComp ℤ

  find-factor g n =
    if even n ∧ (2 <ᵇ n) then return 2 else find-factor-start g n

  find-factor-start g n with randomR (1 , n - 1) g
  ... | a , g2 = Tick λ where .force -> find-factor-aux n a g2 2 ((2 * 2 + a) mod n)

  find-factor-aux n a g2 x y with gcd (x - y) n
  ... | d with d == 1 | d == n
  ...   | true | _ = Tick λ where .force -> find-factor-aux n a g2 (f x) (f (f y))
    where
      f : ℤ -> ℤ
      f x = (x * x + a) mod n
  ...   | false | true = find-factor-start g2 n
  ...   | false | false = return d

-- ----------------------------------------------------------------------
-- * Implementation details

-- Our implementation of the top-level Diophantine equation solvers
-- proceeds through a series of special cases. The following functions
-- handle the special cases, and are not of independent interest.

-- interleave p f k: alternately run the prime solver p for 4 steps
-- and the factoring solver f for 1000 steps, until p returns a result
-- (which is returned), or f returns a factor a (found after c steps),
-- in which case the computation continues as k a c. This is the
-- Haskell function
--
--   interleave p f = do
--     p <- subtask 4 p
--     case p of
--       Done res -> return res
--       _ -> do
--         f <- subtask 1000 f
--         case f of
--           Done (a, k) -> k a c
--           _ -> interleave p f
--
-- written as a state machine: interleave-p m p f k runs p for m+1
-- more steps, and interleave-f m p f k runs f for m+1 more steps.
module _ {R : Set} where
  private
    K = ℤ -> ℕ -> StepComp R

  interleave-p : ℕ -> StepComp R -> StepComp (ℤ × ℕ) -> K -> StepComp R
  interleave-f : ℕ -> StepComp R -> StepComp (ℤ × ℕ) -> K -> StepComp R
  after-p after-f : StepComp R -> StepComp (ℤ × ℕ) -> K -> StepComp R

  interleave-p m (Done res) f k = Done res
  interleave-p zero (Tick p) f k = Tick λ where .force -> after-p (p .force) f k
  interleave-p (suc m) (Tick p) f k = Tick λ where .force -> interleave-p m (p .force) f k

  after-p (Done res) f k = Done res
  after-p p@(Tick _) f k = interleave-f 999 p f k

  interleave-f m p (Done (a , c)) k = k a c
  interleave-f zero p (Tick f) k = Tick λ where .force -> after-f p (f .force) k
  interleave-f (suc m) p (Tick f) k = Tick λ where .force -> interleave-f m p (f .force) k

  after-f p (Done (a , c)) k = k a c
  after-f p f@(Tick _) k = interleave-p 3 p f k

  interleave : StepComp R -> StepComp (ℤ × ℕ) -> K -> StepComp R
  interleave p f k = interleave-p 3 p f k

-- The product of a list.
product : {A : Set} {{_ : SemiRing A}} -> List A -> A
product = foldr _*_ 1#

module _ {G : Set} {{_ : RandomGen G}} where

  -- --------------------------------------------------------------------
  -- ** Case: ξ is an integer

  -- Given an integer n ∈ ℤ, attempt to find t ∈ ℤ[ω] such that t†t ~
  -- n, or return nothing if no such t exists.
  --
  -- This function is optimized for the case when n is prime, and
  -- succeeds in an expected number of 2 ticks in this case. If n is
  -- not prime, this function probably diverges.
  dioph-int-assoc-prime : G -> ℤ -> StepComp (Maybe ZOmega)
  dioph-int-assoc-prime g n' =
    if n == 0 then return (just 0)
    else if n == 2 then return (just roottwo)
    else if n mod 4 == 1 then
      (root-of-negative-one g n >>= λ h ->
       return (just (euclid-gcd {ZOmega} (fromℤ h + i) (fromℤ n))))
    else if n mod 8 == 3 then
      (root-mod g n -2 >>= λ h ->
       return (just (euclid-gcd {ZOmega} (fromℤ h + i * roottwo) (fromℤ n))))
    else if n mod 8 == 7 then
      -- if n is prime, then 2 is a square. Conversely, if 2 is a
      -- square, even if n is not prime, it implies that the
      -- Diophantine equation has no solution. Because in this case, 2
      -- is a square for every prime divisor of n, so each such
      -- divisor must be congruent to 1 or 7 (mod 8), so there must be
      -- at least one prime divisor that occurs as an odd power and is
      -- congruent to 7 mod n.
      (root-mod g n 2 >>= λ _ -> return nothing)
    -- If n is even and not 2, then it is not prime, so diverge.
    else diverge
    where
      n = abs n'

  -- Given an integer n ∈ ℤ, find t ∈ ℤ[ω] such that t†t ~ n, if such t
  -- exists, or return nothing if no such t exists.
  --
  -- This function alternately calls dioph-int-assoc-prime and attempts
  -- to factor n. Therefore, it will eventually succeed; however, the
  -- runtime depends on how hard it is to factor ξ.
  --
  -- The primed versions take the fuel for the recursion on factors.
  dioph-int-assoc' : ℕ -> G -> ℤ -> StepComp (Maybe ZOmega)
  dioph-int-assoc-powers' : ℕ -> G -> List (ℤ × ℕ) -> StepComp (Maybe ZOmega)
  dioph-int-assoc-power' : ℕ -> G -> ℤ × ℕ -> StepComp (Maybe ZOmega)

  dioph-int-assoc' zero g n = diverge
  dioph-int-assoc' (suc fuel) g n' =
    if n == 0 then return (just 0)
    else if n == 1 then return (just 1)
    else interleave prime-solver factor-solver λ a k ->
      forward (k Nat./ 2) (dioph-int-assoc-powers' fuel g3 (proj₂ (relatively-prime-factors a (n div a))))
    where
      n = abs n'
      g1 = proj₁ (split g)
      g' = proj₂ (split g)
      g2 = proj₁ (split g')
      g3 = proj₂ (split g')
      prime-solver = dioph-int-assoc-prime g1 n
      factor-solver = with-counter (speedup 30 (find-factor g2 n))

  -- Given a factorization n = q₁^k₁ ⋯ qₘ^kₘ of an integer n, where
  -- q₁, …, qₘ are pairwise relatively prime, find t ∈ ℤ[ω] such that
  -- t†t ~ n, if such t exists, or return nothing if no such t exists.
  dioph-int-assoc-powers' fuel g facs =
    parallel-list-maybe (map (dioph-int-assoc-power' fuel g) facs) >>= λ where
      nothing -> return nothing
      (just sols) -> return (just (product sols))

  -- Given a pair of integers (n, k), find t ∈ ℤ[ω] such that t†t ~ nᵏ,
  -- if such t exists, or return nothing if no such t exists.
  dioph-int-assoc-power' fuel g (n , k) =
    if evenℕ k then return (just (fromℤ (n ^ (k Nat./ 2))))
    else (dioph-int-assoc' fuel g n >>= λ where
            nothing -> return nothing
            (just t) -> return (just (t ^ k)))

  -- The fuel needed for dioph-int-assoc' on n: every recursive call is
  -- on a proper factor, so the bit length of n suffices.
  int-fuel : ℤ -> ℕ
  int-fuel n = suc (hibit Int.∣ n ∣)

  dioph-int-assoc : G -> ℤ -> StepComp (Maybe ZOmega)
  dioph-int-assoc g n = dioph-int-assoc' (int-fuel n) g n

  dioph-int-assoc-powers : G -> List (ℤ × ℕ) -> StepComp (Maybe ZOmega)
  dioph-int-assoc-powers g facs = dioph-int-assoc-powers' (int-fuel (product (map (λ (n , k) -> n ^ k) facs))) g facs

  dioph-int-assoc-power : G -> ℤ × ℕ -> StepComp (Maybe ZOmega)
  dioph-int-assoc-power g (n , k) = dioph-int-assoc-power' (int-fuel (n ^ k)) g (n , k)

  -- --------------------------------------------------------------------
  -- ** Case: ξ ~ ξ•

  -- Given ξ ∈ ℤ[√2] such that ξ ~ ξ•, find t ∈ ℤ[ω] such that t†t ~ ξ,
  -- if such t exists, or return nothing if no such t exists.
  dioph-zroottwo-selfassociate : G -> ZRootTwo -> StepComp (Maybe ZOmega)
  dioph-zroottwo-selfassociate g xi@(RootTwo a b) =
    if xi == 0 then return (just 0)
    else (dioph-int-assoc g n >>= λ where
            nothing -> return nothing
            (just t) -> if euclid-divides roottwo r
                        then return (just ((1 + omega) * t))
                        else return (just t))
    where
      n = gcd a b
      r = euclid-div xi (fromℤ n)

  -- --------------------------------------------------------------------
  -- ** Case: gcd(ξ, ξ•) = 1

  -- Given ξ ∈ ℤ[√2] such that gcd(ξ, ξ•) = 1, attempt to find t ∈ ℤ[ω]
  -- such that t†t ~ ξ, or return nothing if no such t exists.
  --
  -- This function is optimized for the case when ξ is a prime in the
  -- ring ℤ[√2]. In this case, it succeeds quickly, in an expected
  -- number of 2 ticks. If ξ is not prime, this function probably
  -- diverges.
  dioph-zroottwo-assoc-prime : G -> ZRootTwo -> StepComp (Maybe ZOmega)
  dioph-zroottwo-assoc-prime g xi =
    if xi == 0 then return (just 0)
    else if n mod 8 == 1 then
      (root-of-negative-one g n >>= λ h ->
       return (just (euclid-gcd {ZOmega} (fromℤ h + i) (fromZRootTwo xi))))
    else if n mod 8 == 7 then return nothing
    else diverge
    where
      n = abs (norm xi)

  -- Given ξ ∈ ℤ[√2] such that gcd(ξ, ξ•) = 1, find t ∈ ℤ[ω] such that
  -- t†t ~ ξ, if such t exists, or return nothing if no such t exists.
  --
  -- This function alternately calls dioph-zroottwo-assoc-prime and
  -- attempts to factor ξ. Therefore, it will eventually succeed.
  -- However, the runtime depends on how hard it is to factor ξ.
  --
  -- The primed versions take the fuel for the recursion on factors.
  dioph-zroottwo-assoc' : ℕ -> G -> ZRootTwo -> StepComp (Maybe ZOmega)
  dioph-zroottwo-assoc-powers' : ℕ -> G -> List (ZRootTwo × ℕ) -> StepComp (Maybe ZOmega)
  dioph-zroottwo-assoc-power' : ℕ -> G -> ZRootTwo × ℕ -> StepComp (Maybe ZOmega)

  dioph-zroottwo-assoc' zero g xi = diverge
  dioph-zroottwo-assoc' (suc fuel) g xi =
    if xi == 0 then return (just 0)
    else interleave prime-solver factor-solver λ a k ->
      case euclid-gcd xi (fromℤ a) of λ alpha ->
      forward (k Nat./ 2) (dioph-zroottwo-assoc-powers' fuel g3 (proj₂ (relatively-prime-factors alpha (euclid-div xi alpha))))
    where
      g1 = proj₁ (split g)
      g' = proj₂ (split g)
      g2 = proj₁ (split g')
      g3 = proj₂ (split g')
      n = abs (norm xi)
      prime-solver = dioph-zroottwo-assoc-prime g1 xi
      factor-solver = with-counter (speedup 30 (find-factor g2 n))

  -- Given a factorization ξ = q₁^k₁ ⋯ qₘ^kₘ of some ξ ∈ ℤ[√2], where
  -- q₁, …, qₘ are pairwise relatively prime, find t ∈ ℤ[ω] such that
  -- t†t ~ ξ, if such t exists, or return nothing if it can be proven
  -- not to exist.
  dioph-zroottwo-assoc-powers' fuel g facs =
    parallel-list-maybe (map (dioph-zroottwo-assoc-power' fuel g) facs) >>= λ where
      nothing -> return nothing
      (just sols) -> return (just (product sols))

  -- Given a pair (ξ, k), with ξ ∈ ℤ[√2] and k ≥ 0, find t ∈ ℤ[ω] such
  -- that t†t ~ ξᵏ, if such t exists, or return nothing if no such t
  -- exists.
  dioph-zroottwo-assoc-power' fuel g (xi , k) =
    if evenℕ k then return (just (fromZRootTwo (xi ^ (k Nat./ 2))))
    else (dioph-zroottwo-assoc' fuel g xi >>= λ where
            nothing -> return nothing
            (just t) -> return (just (t ^ k)))

  -- The fuel needed for dioph-zroottwo-assoc' on ξ: every recursive
  -- call is on a proper factor, so the bit length of the norm suffices.
  zroottwo-fuel : ZRootTwo -> ℕ
  zroottwo-fuel xi = suc (hibit (rank xi))

  dioph-zroottwo-assoc : G -> ZRootTwo -> StepComp (Maybe ZOmega)
  dioph-zroottwo-assoc g xi = dioph-zroottwo-assoc' (zroottwo-fuel xi) g xi

  dioph-zroottwo-assoc-powers : G -> List (ZRootTwo × ℕ) -> StepComp (Maybe ZOmega)
  dioph-zroottwo-assoc-powers g facs =
    dioph-zroottwo-assoc-powers' (zroottwo-fuel (product (map (λ (xi , k) -> xi ^ k) facs))) g facs

  dioph-zroottwo-assoc-power : G -> ZRootTwo × ℕ -> StepComp (Maybe ZOmega)
  dioph-zroottwo-assoc-power g (xi , k) = dioph-zroottwo-assoc-power' (zroottwo-fuel (xi ^ k)) g (xi , k)

  -- --------------------------------------------------------------------
  -- * Diophantine solvers

  -- Given ξ ∈ ℤ[√2], find t ∈ ℤ[ω] such that t†t ~ ξ, if such t
  -- exists, or nothing otherwise. Unlike diophantine, the equation is
  -- only solved up to associates, i.e., up to a unit of the ring.
  diophantine-associate : G -> ZRootTwo -> StepComp (Maybe ZOmega)
  diophantine-associate g xi =
    if xi == 0 then return (just 0)
    else with-d (euclid-gcd xi (adj2 xi))
    where
      g1 = proj₁ (split g)
      g2 = proj₂ (split g)
      -- (d is passed as an argument, so that it is computed only once;
      -- where-bound values are not shared in compiled code.)
      with-d : ZRootTwo -> StepComp (Maybe ZOmega)
      with-d d =
        parallel-maybe (dioph-zroottwo-selfassociate g1 d) (dioph-zroottwo-assoc g2 (euclid-div xi d)) >>= λ where
          nothing -> return nothing
          (just (t1 , t2)) -> return (just (t1 * t2))

  -- Given ξ ∈ ℤ[√2], find t ∈ ℤ[ω] such that t†t = ξ, if such t
  -- exists, or return nothing otherwise.
  diophantine : G -> ZRootTwo -> StepComp (Maybe ZOmega)
  diophantine g xi =
    if xi == 0 then return (just 0)
    else if xi <ᵇ 0 then return nothing
    else if adj2 xi <ᵇ 0 then return nothing
    else (diophantine-associate g xi >>= λ where
      nothing -> return nothing
      (just t) -> case zroottwo-of-zomega (adj t * t) of λ where
        -- impossible, since t†t is real
        nothing -> return nothing
        (just xi-associate) -> case zroottwo-root (euclid-div xi xi-associate) of λ where
          nothing -> return nothing
          (just v) -> return (just (fromZRootTwo v * t)))

  -- Given an element ξ ∈ 𝔻[√2], find t ∈ 𝔻[ω] such that t†t = ξ, if
  -- such t exists, or return nothing otherwise.
  --
  -- Implementation note: In the reduction from 𝔻[√2] to ℤ[√2], we can
  -- multiply by a power of λ√2 instead of √2. This has the same effect
  -- of reducing the denominator exponent to 0 (note that λ is a unit
  -- of the ring ℤ[√2]), but has the additional advantage that λ√2
  -- (unlike √2) is doubly positive, thereby preserving solvability of
  -- the Diophantine equation.
  --
  -- Similarly, in translating the solution back from ℤ[ω] to 𝔻[ω], we
  -- use the fact that 1/(λ√2) = u†u, where u = (ω - i)/√2. Also note
  -- that u = δ⁻¹, where δ = 1 + ω.
  diophantine-dyadic : G -> DRootTwo -> StepComp (Maybe DOmega)
  --
  -- (Performance: k' and k'' are passed as arguments, since where-bound
  -- values are not shared in compiled code. Haskell computes ξ' =
  -- to_whole ((λ√2)^k'' * 2^k' * ξ); we compute the same value
  -- ⌊2^k' ⋅ (λ√2)^k'' ξ⌋ (coefficient-wise) with integer-of-dyadic,
  -- which avoids normalizing the dyadic fractions of 2^k' ⋅ ...)
  diophantine-dyadic g xi = with-k (denomexp xi)
    where
      u : DOmega
      u = roothalf * (omega - i)
      lambda : DRootTwo
      lambda = 1 + roottwo
      times-2^ : ℕ -> DRootTwo -> ZRootTwo
      times-2^ k' (RootTwo x y) = RootTwo (integer-of-dyadic x k') (integer-of-dyadic y k')
      with-k' : ℕ -> ℕ -> StepComp (Maybe DOmega)
      with-k' k' k'' =
        diophantine g (times-2^ k' ((lambda * roottwo) ^ k'' * xi)) >>= λ where
          nothing -> return nothing
          (just t') -> return (just (u ^ k'' * roothalf ^ k' * from-whole t'))
      with-k : ℕ -> StepComp (Maybe DOmega)
      with-k k = with-k' (k Nat./ 2) (k Nat.% 2)
