-- This module is an Agda port of the module Quantum.Synthesis.GridSynth
-- of the Haskell package newsynth (by N. J. Ross and P. Selinger).
--
-- It implements the approximate single-qubit synthesis algorithm of
--
-- * N. J. Ross and P. Selinger, "Optimal ancilla-free Clifford+T
--   approximation of z-rotations". http://arxiv.org/abs/1403.2975.
--
-- The algorithm is near-optimal in the following sense: it produces
-- an operator whose expected T-count exceeds the T-count of the
-- second-to-optimal solution to the approximate synthesis problem by
-- at most O(log(log(1/ε))).
--
-- Differences from the Haskell version:
--
-- * Haskell's Double is Float. The candidate information returns the
--   T-counts as ℕ (Haskell: Integer; they are never negative).
--
-- * The precision of the internal computations: as in Haskell,
--   gridsynth-stats computes digits = ⌈15 + 2.5⋅b⋅log₁₀ 2⌉ (with Float
--   arithmetic) and converts the precision b and the angle θ to
--   FixedPrec digits (dynamic-fixedprec2 of ToReal; the precision is a
--   term in Agda).
--
-- * The infinite list of candidates of Haskell's gridsynth_internal
--   is a Stream (see GridProblems: gridpoints2-increasing). The
--   candidates are consumed lazily, level by level (level k = the
--   solutions with denominator exponent k), until a candidate's
--   Diophantine equation is solved within "effort" steps. The number
--   of levels examined is bounded by gridsynth-level-fuel (10⁶; for
--   ε = 2⁻ᵇ about 3b + O(1) levels are needed, and each level
--   contains candidates once k is large enough). Should the fuel run
--   out (which cannot happen in practice), the result is the identity
--   matrix with no error estimate (Haskell would keep searching). The
--   Haskell error "finite list of candidates" cannot occur for a
--   stream.
--
-- * mergeBy and first are ported for lists; the phase version merges
--   the two candidate streams with mergeBy-stream.
--
-- * Performance: where-bound values are not shared in compiled Agda,
--   so the constants of the ε-region (cos(-θ/2), sin(-θ/2), the
--   center distance, the eigenvalues) are computed once and passed as
--   arguments to the helper that builds the convex set, and ε itself
--   is computed once and passed on.

{-# OPTIONS --without-K --safe --guardedness #-}

module Quantum.Synthesis.GridSynth where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ)
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String ; _++_)
open import Data.Unit.Base using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no)
open import Codata.Guarded.Stream as Stream using (Stream)
open Stream.Stream using (head ; tail)

open import Instances
open import Literals
open import Data.Number.FixedPrec
open Data.Number.FixedPrec.Aux using (divide)
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.FixedPrec
open import Quantum.Synthesis.Matrix
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.GridProblems
open import Quantum.Synthesis.Diophantine
open import Quantum.Synthesis.StepComp
open import Quantum.Synthesis.QuadraticEquation
open import Quantum.Synthesis.Random using (RandomGen ; split)

-- ----------------------------------------------------------------------
-- * Auxiliary types

-- Information about the status of an attempt to solve a Diophantine
-- equation. Success means the Diophantine equation was solved; Fail
-- means that it was proved that there was no solution; Timeout means
-- that the question was not decided within the allotted time.
data DStatus : Set where
  Success Fail Timeout : DStatus

instance
  ShowDStatus : Show DStatus
  ShowDStatus .showsPrec _ Success = "Success"
  ShowDStatus .showsPrec _ Fail = "Fail"
  ShowDStatus .showsPrec _ Timeout = "Timeout"

  DecEqDStatus : DecEq DStatus
  DecEqDStatus ._≟_ Success Success = yes refl
  DecEqDStatus ._≟_ Fail Fail = yes refl
  DecEqDStatus ._≟_ Timeout Timeout = yes refl
  DecEqDStatus ._≟_ Success Fail = no λ ()
  DecEqDStatus ._≟_ Success Timeout = no λ ()
  DecEqDStatus ._≟_ Fail Success = no λ ()
  DecEqDStatus ._≟_ Fail Timeout = no λ ()
  DecEqDStatus ._≟_ Timeout Success = no λ ()
  DecEqDStatus ._≟_ Timeout Fail = no λ ()

-- The information on the candidates tried: (u, T-count, status), most
-- recent first.
CandidateInfo : Set
CandidateInfo = List (DOmega × ℕ × DStatus)

-- The result of the gridsynth-stats functions: the operator, log₀.₅
-- of the actual approximation error (or nothing if the error is 0),
-- and the candidate information.
GridSynthResult : Set
GridSynthResult = U2 DOmega × Maybe Float × CandidateInfo

-- The phase of a candidate in gridsynth-phase-internal.
data Phase : Set where
  Phase0 Phase1 : Phase

-- Haskell's Ordering.
data Ordering : Set where
  LT EQ GT : Ordering

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- Merge the elements of two lists in increasing order, assuming that
-- each of the lists is already sorted. The first argument is a
-- comparison function for elements.
mergeBy : {A : Set} -> (A -> A -> Ordering) -> List A -> List A -> List A
mergeBy {A} c l1 l2 = go (List.length l1 Nat.+ List.length l2) l1 l2
  where
    -- the first argument is fuel (the total length suffices).
    go : ℕ -> List A -> List A -> List A
    go _ [] l2 = l2
    go _ l1 [] = l1
    go zero l1 l2 = l1 List.++ l2
    go (suc f) (h1 ∷ t1) (h2 ∷ t2) with c h1 h2
    ... | LT = h1 ∷ go f t1 (h2 ∷ t2)
    ... | _ = h2 ∷ go f (h1 ∷ t1) t2

-- The same for (infinite) streams.
mergeBy-stream : {A : Set} -> (A -> A -> Ordering) -> Stream A -> Stream A -> Stream A
merge-step : {A : Set} -> (A -> A -> Ordering) -> Ordering -> Stream A -> Stream A -> Stream A
mergeBy-stream c s1 s2 = merge-step c (c (head s1) (head s2)) s1 s2
merge-step c LT s1 s2 .head = head s1
merge-step c LT s1 s2 .tail = mergeBy-stream c (tail s1) s2
merge-step c EQ s1 s2 .head = head s2
merge-step c EQ s1 s2 .tail = mergeBy-stream c s1 (tail s2)
merge-step c GT s1 s2 .head = head s2
merge-step c GT s1 s2 .tail = mergeBy-stream c s1 (tail s2)

-- Return the first component of a triple.
first : {A B C : Set} -> A × B × C -> A
first (a , _ , _) = a

private
  compareℕ : ℕ -> ℕ -> Ordering
  compareℕ m n = if m Nat.<ᵇ n then LT else if n Nat.<ᵇ m then GT else EQ

  -- The T-count of a candidate with denominator exponent k.
  tcount : ℕ -> ℕ
  tcount zero = 0
  tcount k@(suc _) = 2 Nat.* k Nat.∸ 2

  -- δ⁻¹ = (ω - i)/√2, used by gridsynth-phase-internal. (A top-level
  -- constant, so that it is computed only once in compiled code.)
  delta-inv : DOmega
  delta-inv = roothalf * (omega - i)

-- The number of levels (denominator exponents) of candidates examined
-- by gridsynth-internal and gridsynth-phase-internal before giving
-- up. For ε = 2⁻ᵇ, about 3b + O(1) levels are needed.
gridsynth-level-fuel : ℕ
gridsynth-level-fuel = 1000000

-- ----------------------------------------------------------------------
-- * The ε-region

module _ {R : Set} {{_ : Ring R}} {{_ : DecEq R}} {{_ : DecOrd R}} {{_ : Fractional R}} {{_ : RootHalfRing R}}
         {{_ : Floating R}} {{_ : Quadratic QRootTwo R}} where
  open LiteralsFor R

  private
    -- The ε-region scaled by √s, given the precomputed constants: the
    -- eigenvalues ev1, ev2 of the bounding ellipse, z = (zx, zy), and
    -- the distance rd of the cutting line from the origin.
    epsilon-region-mk : DRootTwo -> R -> R -> R -> R -> R -> ConvexSet R
    epsilon-region-mk s ev1 ev2 zx zy rd = ConvexSet' (Ellipse' mat (rd * zx , rd * zy)) tst int
      where
        bmat : Operator R
        bmat = toOperator ((zx , - zy) , (zy , zx))
        mat : Operator R
        mat = bmat * toOperator ((ev1 , 0) , (0 , ev2)) * special-inverse bmat

        -- The characteristic function of the ε-region.
        tst : CharFun
        tst (x , y) = (x ^ 2 + y ^ 2 ≤ᵇ s) ∧ (rd ≤ᵇ zx * fromDRootTwo x + zy * fromDRootTwo y)

        -- A line intersector for the ε-region.
        int : LineIntersector R
        int p v = go (quadratic (fromDRootTwo {QRootTwo} a) (fromDRootTwo b) (fromDRootTwo c))
                     (iprod (point-fromDRootTwo v) (zx , zy)) (rd - iprod (point-fromDRootTwo p) (zx , zy))
          where
            a b c : DRootTwo
            a = iprod v v
            b = 2 * iprod v p
            c = iprod p p - s
            -- solve (p + tv) ⋅ z ≥ rd, equivalently t ⋅ vz ≥ rd - p⋅z = rhs.
            go : Maybe (R × R) -> R -> R -> Maybe (R × R)
            go nothing vz rhs = nothing
            go (just (t0 , t1)) vz rhs =
              if (vz == 0) ∧ (rhs ≤ᵇ 0) then just (t0 , t1)
              else if vz == 0 then nothing
              else if 0 <ᵇ vz then just (max t0 (divide rhs vz) , t1)
              else just (t0 , min t1 (divide rhs vz))

    epsilon-region-z : R -> R -> R -> ConvexSet R
    epsilon-region-z epsilon zx zy =
      epsilon-region-mk 1 (4 * divide 1 epsilon ^ 4) (divide 1 epsilon ^ 2) zx zy (1 - divide (epsilon ^ 2) 2)

    epsilon-region-scaled-z : DRootTwo -> R -> R -> R -> R -> ConvexSet R
    epsilon-region-scaled-z s fs epsilon zx zy =
      epsilon-region-mk s (divide (4 * divide 1 epsilon ^ 4) fs) (divide (divide 1 epsilon ^ 2) fs) zx zy
        ((1 - divide (epsilon ^ 2) 2) * sqrt fs)

  -- The ε-region for given ε and θ is a convex subset of the closed
  -- unit disk, given by u ⋅ z ≥ 1 - ε²/2, where z = exp(-iθ/2), and
  -- "⋅" denotes the dot product of ℝ² (identified with ℂ).
  epsilon-region : R -> R -> ConvexSet R
  epsilon-region epsilon theta = mk (- divide theta 2)
    where
      mk : R -> ConvexSet R
      mk h = epsilon-region-z epsilon (cos h) (sin h)

  -- The ε-region, scaled by an additional factor of √s, where s > 0.
  -- The center of scaling is the origin.
  epsilon-region-scaled : DRootTwo -> R -> R -> ConvexSet R
  epsilon-region-scaled s epsilon theta = mk (- divide theta 2)
    where
      mk : R -> ConvexSet R
      mk h = epsilon-region-scaled-z s (fromDRootTwo s) epsilon (cos h) (sin h)

-- ----------------------------------------------------------------------
-- * Main algorithm implementation

module _ {R : Set} {{_ : Ring R}} {{_ : DecEq R}} {{_ : DecOrd R}} {{_ : Fractional R}} {{_ : Floor R}}
         {{_ : RootTwoRing R}} {{_ : RootHalfRing R}} {{_ : HalfRing R}} {{_ : Floating R}}
         {{_ : Adjoint R}} {{_ : ToRational R}} {{_ : Quadratic QRootTwo R}}
         {G : Set} {{_ : RandomGen G}} where
  open LiteralsFor R

  private
    -- log₀.₅ of the error, or nothing if the error is 0.
    log-err-of : R -> Maybe Float
    log-err-of err = if err ≤ᵇ 0 then nothing else just (logBase-double half err)

    -- The error of an approximation U of Rz(θ) (up to the scalar
    -- factor sc): √(‖sc⋅U - Rz(θ)‖²_HS / 2).
    approx-error : R [i] -> R -> U2 DOmega -> R
    approx-error sc theta uU =
      sqrt (divide (real (hs-sqnorm ((sc scalarmult matrix-map fromDOmega uU) ·-· zrot theta))) 2)

    success0 : R -> DOmega -> DOmega -> U2 DOmega × Maybe Float
    success0 theta u t = mk (if denomexp (u + t) <ᵇ denomexp (u + omega * t)
                              then matrix2x2 (u , - adj t) (t , adj u)
                              else matrix2x2 (u , - adj (omega * t)) (omega * t , adj u))
      where
        mk : U2 DOmega -> U2 DOmega × Maybe Float
        mk uU = uU , log-err-of (approx-error 1 theta uU)

    omega-inv : DOmega
    omega-inv = omega ^ 7

    success1 : R -> DOmega -> DOmega -> U2 DOmega × Maybe Float
    success1 theta u t = mk (if denomexp (u + t) <ᵇ denomexp (u + omega * t)
                              then matrix2x2 (u , - adj t * omega-inv) (t , adj u * omega-inv)
                              else matrix2x2 (u , - adj t) (t * omega-inv , adj u * omega-inv))
                            (Cplx (cos (divide pi 8)) (sin (divide pi 8)))
      where
        mk : U2 DOmega -> R [i] -> U2 DOmega × Maybe Float
        mk uU sqrt-omega = uU , log-err-of (approx-error sqrt-omega theta uU)

    -- The result when the candidate u succeeded with solution t.
    result : CandidateInfo -> DOmega -> ℕ -> U2 DOmega × Maybe Float -> GridSynthResult
    result info u tc (uU , log-err) = uU , log-err , (u , tc , Success) ∷ info

    -- The result when the level fuel ran out (never happens).
    no-result : CandidateInfo -> GridSynthResult
    no-result info = 1 , nothing , info

    -- ξ = Re(1 - u†u), the right-hand side of the Diophantine equation
    -- t†t = ξ for the candidate u.
    xi-of : DOmega -> DRootTwo
    xi-of u = real (1 - adj u * u)

    -- Search the candidate levels (tcount, phase, us) of a stream for
    -- the first solvable candidate. The arguments are: the level fuel,
    -- the callback for success, the effort, the candidate info so far,
    -- the generator, the current T-count and phase, the remaining
    -- candidates of the current level, and the stream of the following
    -- levels. (Helper functions are used instead of "with", which
    -- made the type checker unfold the step computation.)
    first-solvable : {P : Set} -> ℕ -> (P -> DOmega -> DOmega -> U2 DOmega × Maybe Float) -> ℕ ->
                     CandidateInfo -> G -> ℕ -> P -> List DOmega -> Stream (ℕ × P × List DOmega) -> GridSynthResult
    fs-try : {P : Set} -> ℕ -> (P -> DOmega -> DOmega -> U2 DOmega × Maybe Float) -> ℕ ->
             CandidateInfo -> ℕ -> P -> DOmega -> List DOmega -> Stream (ℕ × P × List DOmega) -> G × G -> GridSynthResult
    fs-check : {P : Set} -> ℕ -> (P -> DOmega -> DOmega -> U2 DOmega × Maybe Float) -> ℕ ->
               CandidateInfo -> ℕ -> P -> DOmega -> List DOmega -> Stream (ℕ × P × List DOmega) -> G ->
               Maybe (Maybe DOmega) -> GridSynthResult
    fs-next : {P : Set} -> ℕ -> (P -> DOmega -> DOmega -> U2 DOmega × Maybe Float) -> ℕ ->
              CandidateInfo -> G -> ℕ × P × List DOmega -> Stream (ℕ × P × List DOmega) -> GridSynthResult

    first-solvable fuel ok effort info g tc ph (u ∷ us) s = fs-try fuel ok effort info tc ph u us s (split g)
    first-solvable zero ok effort info g tc ph [] s = no-result info
    first-solvable (suc fuel) ok effort info g tc ph [] s = fs-next fuel ok effort info g (head s) (tail s)

    fs-next fuel ok effort info g (tc , ph , us) s = first-solvable fuel ok effort info g tc ph us s

    fs-try fuel ok effort info tc ph u us s (g1 , g2) =
      fs-check fuel ok effort info tc ph u us s g2 (run-bounded effort (diophantine-dyadic g1 (xi-of u)))

    fs-check fuel ok effort info tc ph u us s g2 (just (just t)) = result info u tc (ok ph u t)
    fs-check fuel ok effort info tc ph u us s g2 (just nothing) =
      first-solvable fuel ok effort ((u , tc , Fail) ∷ info) g2 tc ph us s
    fs-check fuel ok effort info tc ph u us s g2 nothing =
      first-solvable fuel ok effort ((u , tc , Timeout) ∷ info) g2 tc ph us s

    level0 : ℕ × List DOmega -> ℕ × ⊤ × List DOmega
    level0 (k , us) = tcount k , tt , us

  -- The internal implementation of the ellipse-based approximate
  -- synthesis algorithm. The parameters are a source of randomness g,
  -- the angle θ, the precision b ≥ 0 in bits, and an amount of
  -- "effort" to put into factoring.
  --
  -- The outputs are a unitary operator in the Clifford+T group that
  -- approximates Rz(θ) to within ε in the operator norm; log₀.₅ of
  -- the actual error, or nothing if the error is 0; and the
  -- information on the candidates tried.
  --
  -- Note: the parameter θ must be of a real number type that has
  -- enough precision to perform intermediate calculations; this
  -- typically requires precision O(ε²). A more user-friendly function
  -- that selects the required precision automatically is gridsynth.
  gridsynth-internal : G -> R -> R -> ℕ -> GridSynthResult
  gridsynth-internal g prec theta effort = go (2 ** (- prec))
    where
      go : R -> GridSynthResult
      go epsilon =
        first-solvable gridsynth-level-fuel (λ _ -> success0 theta) effort [] g 0 tt []
          (Stream.map level0 (gridpoints2-increasing (epsilon-region epsilon theta) unitdisk))

  -- The internal implementation of the ellipse-based approximate
  -- synthesis algorithm, up to a phase. The parameters are the same as
  -- for gridsynth-internal.
  gridsynth-phase-internal : G -> R -> R -> ℕ -> GridSynthResult
  gridsynth-phase-internal g prec theta effort = go (2 ** (- prec))
    where
      ok : Phase -> DOmega -> DOmega -> U2 DOmega × Maybe Float
      ok Phase0 = success0 theta
      ok Phase1 = success1 theta

      lev0 : ℕ × List DOmega -> ℕ × Phase × List DOmega
      lev0 (k , us) = tcount k , Phase0 , us

      lev1 : ℕ × List DOmega -> ℕ × Phase × List DOmega
      lev1 (k , us) = suc (tcount k) , Phase1 , List.map (_* delta-inv) us

      search : ConvexSet R -> ConvexSet R -> Operator DRootTwo -> GridSynthResult
      search region0 region1 opG =
        first-solvable gridsynth-level-fuel ok effort [] g 0 Phase0 []
          (mergeBy-stream (λ x y -> compareℕ (first x) (first y))
            (Stream.map lev0 (gridpoints2-increasing-with-gridop region0 unitdisk opG))
            (Stream.map lev1 (gridpoints2-increasing-with-gridop region1 (disk (2 - roottwo)) opG)))

      go2 : ConvexSet R -> ConvexSet R -> GridSynthResult
      go2 region0 region1 = search region0 region1 (to-upright-sets region0 unitdisk)

      go : R -> GridSynthResult
      go epsilon = go2 (epsilon-region epsilon theta) (epsilon-region-scaled (2 + roottwo) epsilon theta)

-- ----------------------------------------------------------------------
-- * User-friendly functions

private
  -- The number of decimal digits used for the internal computations
  -- at precision b: ⌈15 + 2.5⋅b⋅log₁₀ 2⌉ (a heuristic formula!).
  gridsynth-digits : Float -> ℤ
  gridsynth-digits prec = float-ceiling (15.0 Float.+ 2.5 Float.* prec Float.* logBase 10.0 2.0)

-- A version of gridsynth that also returns some statistics: log₀.₅ of
-- the actual approximation error (or nothing if the error is 0), and
-- a data structure with information on the candidates tried.
gridsynth-stats : {G : Set} {{_ : RandomGen G}} -> G -> Float -> SymReal -> ℕ -> GridSynthResult
gridsynth-stats g prec theta effort =
  dynamic-fixedprec2 (gridsynth-digits prec) (λ p t -> gridsynth-internal g p t effort) prec theta

-- A version of gridsynth-stats that returns the optimal operator up
-- to a global phase. (The default behavior is to return the optimal
-- operator exactly).
gridsynth-phase-stats : {G : Set} {{_ : RandomGen G}} -> G -> Float -> SymReal -> ℕ -> GridSynthResult
gridsynth-phase-stats g prec theta effort =
  dynamic-fixedprec2 (gridsynth-digits prec) (λ p t -> gridsynth-phase-internal g p t effort) prec theta

-- Output a unitary operator in the Clifford+T group that approximates
-- Rz(θ) = exp(-iθZ/2) to within ε in the operator norm. This operator
-- can then be converted to a list of gates with to-gates.
--
-- The parameters are:
--
-- * a source of randomness g;
-- * the precision b ≥ 0 in bits, such that ε = 2⁻ᵇ;
-- * the angle θ;
-- * an integer that determines the amount of "effort" to put into
--   factoring. A larger number means more time spent on factoring. A
--   good default for this is 25.
--
-- Note: the argument θ is given as a symbolic real number. It will
-- automatically be expanded to as many digits as are necessary for
-- the internal calculation. In this way, the caller can specify,
-- e.g., an angle of pi/128 as a SymReal, without having to worry
-- about how many digits of π to specify.
gridsynth : {G : Set} {{_ : RandomGen G}} -> G -> Float -> SymReal -> ℕ -> U2 DOmega
gridsynth g prec theta effort = proj₁ (gridsynth-stats g prec theta effort)

-- A version of gridsynth that returns a list of gates instead of a
-- matrix.
--
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
gridsynth-gates : {G : Set} {{_ : RandomGen G}} -> G -> Float -> SymReal -> ℕ -> List Gate
gridsynth-gates g prec theta effort = synthesis-u2 (gridsynth g prec theta effort)
