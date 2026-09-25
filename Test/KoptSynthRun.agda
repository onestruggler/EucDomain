-- Validation of Kopt.Synth against the authors' experimental data
-- (Kopt/Haskell/experiment_data.dat of github.com/onestruggler/Kopt,
-- Section VI of the paper).
--
-- Each of the 12000 lines of the file is a record
--
--   ((l, [[(re,im) ×4] ×4]), ourCS, glaudellCS, ourK, glaudellK)
--
-- where the listed integral matrix is M = γˡ·U, i.e. the operator is
-- U = M/γˡ. For every record we check
--
--   (a) lde U = l,
--   (b) ⟦synth U⟧ = U, exactly (including the global phase),
--   (c) kc (synth U) = ourK,
--   (d) csc (synth U) = ourCS,
--   (e) kc (synth U) = prkc U   (Lemma IV.7, Table II),
--   (f) the refinement of U puts the residue matrix in the normal
--       form documented in the authors' code,
--   (g) csc (synth U) <= kc + 1 and rlen (synth U) <= 10 kc + 9
--       (Corollary V.8),
--   (h) lde - 2 <= csc (synth U) <= 2 lde + 1 (Remark V.11),
--   (i) the same as (f) with the unitarity-restricted list of normal
--       forms (Kopt.Patterns.normal-forms-unitary), which cuts the 16
--       combinations that pattern (ii) at lde 1 allows down to the
--       two that a unitary operator can have.
--
-- Usage: agda-run.sh Test/KoptSynthRun.agda PATH [COUNT]
-- where PATH is the data file and COUNT limits the number of records.

{-# OPTIONS --guardedness #-}

module Test.KoptSynthRun where

open import IO
open import System.Environment using (getArgs)

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc ; _∸_)
open import Data.Integer.Base as Int using (ℤ ; +_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as Str using (String)
import Data.Unit.Polymorphic.Base as PU
open import Level using (0ℓ)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations
open import Kopt.Patterns
open import Kopt.Synth

-- ----------------------------------------------------------------------
-- * A tiny scanner for signed decimal integers

private
  digit-val : Char -> ℕ
  digit-val c = Char.toℕ c ∸ 48

  -- Read the digits at the head of the list.
  read-nat : ℕ -> List Char -> ℕ × List Char
  read-nat a [] = a , []
  read-nat a (c ∷ cs) =
    if Char.isDigit c then read-nat (a Nat.* 10 Nat.+ digit-val c) cs else (a , c ∷ cs)

  -- All signed integers occurring in a list of characters, in order.
  -- The first argument is fuel; the length of the list will do, since
  -- every step consumes at least one character.
  line-ints : ℕ -> List Char -> List ℤ
  emit-pos emit-neg : ℕ -> ℕ × List Char -> List ℤ

  line-ints zero cs = []
  line-ints (suc n) [] = []
  line-ints (suc n) (c ∷ cs) with Char.isDigit c
  ... | true = emit-pos n (read-nat (digit-val c) cs)
  ... | false with c Char.≈ᵇ '-'
  ...   | false = line-ints n cs
  ...   | true with cs
  ...     | [] = []
  ...     | (d ∷ ds) with Char.isDigit d
  ...       | false = line-ints n cs
  ...       | true = emit-neg n (read-nat (digit-val d) ds)

  emit-pos n (v , rest) = (+ v) ∷ line-ints n rest
  emit-neg n (v , rest) = Int.- (+ v) ∷ line-ints n rest

  ints-of-string : String -> List ℤ
  ints-of-string s = ints-of-chars (Str.toList s)
    where
      ints-of-chars : List Char -> List ℤ
      ints-of-chars cs = line-ints (List.length cs) cs

  nat-of-string : String -> ℕ
  nat-of-string s = proj₁ (read-nat 0 (Str.toList s))

-- ----------------------------------------------------------------------
-- * Records

private
  -- lde, the integral matrix M = γˡ·U (given by rows), our CS-count,
  -- Glaudell's CS-count, our K-count, Glaudell's K-count.
  record Record : Set where
    constructor record'
    field
      rec-lde : ℕ
      rec-mat : Matrix 4 4 ZComplex
      rec-cs : ℕ
      rec-k : ℕ
  open Record

  -- Parse the 37 integers of a record.
  parse-record : List ℤ -> Maybe Record
  parse-record ( l
               ∷ a₀ ∷ b₀ ∷ a₁ ∷ b₁ ∷ a₂ ∷ b₂ ∷ a₃ ∷ b₃
               ∷ c₀ ∷ d₀ ∷ c₁ ∷ d₁ ∷ c₂ ∷ d₂ ∷ c₃ ∷ d₃
               ∷ e₀ ∷ f₀ ∷ e₁ ∷ f₁ ∷ e₂ ∷ f₂ ∷ e₃ ∷ f₃
               ∷ g₀ ∷ h₀ ∷ g₁ ∷ h₁ ∷ g₂ ∷ h₂ ∷ g₃ ∷ h₃
               ∷ ourcs ∷ jcs ∷ ourk ∷ jk ∷ []) =
    just (record' Int.∣ l ∣
                  (matrix4x4 (Cplx a₀ b₀ , Cplx a₁ b₁ , Cplx a₂ b₂ , Cplx a₃ b₃)
                             (Cplx c₀ d₀ , Cplx c₁ d₁ , Cplx c₂ d₂ , Cplx c₃ d₃)
                             (Cplx e₀ f₀ , Cplx e₁ f₁ , Cplx e₂ f₂ , Cplx e₃ f₃)
                             (Cplx g₀ h₀ , Cplx g₁ h₁ , Cplx g₂ h₂ , Cplx g₃ h₃))
                  Int.∣ ourcs ∣ Int.∣ ourk ∣)
  parse-record _ = nothing

  -- U = M/γˡ. The scalar γ⁻ˡ is computed once.
  scale-from-whole : DComplex -> ZComplex -> DComplex
  scale-from-whole g z = from-whole z * g

  operator-of : Record -> Matrix 4 4 DComplex
  operator-of r = matrix-map (scale-from-whole ((1/γ) ^ rec-lde r)) (rec-mat r)

-- ----------------------------------------------------------------------
-- * The checks

private
  -- The checks for one record; true means "passed".
  record Result : Set where
    constructor result
    field
      ok-lde ok-exact ok-k ok-cs ok-prkc ok-norm ok-bounds ok-remark ok-unit : Bool
  open Result

  -- Note that the circuit is passed as an argument, so that synth is
  -- run only once per record.
  check-with : Record -> Matrix 4 4 DComplex -> Circuit -> Result
  check-with r u c =
    result (lde u Nat.≡ᵇ rec-lde r)
           (⟦ c ⟧ == u)
           (kc c Nat.≡ᵇ rec-k r)
           (csc c Nat.≡ᵇ rec-cs r)
           (kc c Nat.≡ᵇ prkc u)
           (refine-normal-form? u)
           ((csc c Nat.≤ᵇ suc (kc c)) ∧ (rlen c Nat.≤ᵇ (10 Nat.* kc c Nat.+ 9)))
           ((rec-lde r ∸ 2 Nat.≤ᵇ csc c) ∧ (csc c Nat.≤ᵇ suc (2 Nat.* rec-lde r)))
           (refine-normal-form-unitary? u)

  check-op : Record -> Matrix 4 4 DComplex -> Result
  check-op r u = check-with r u (synth u)

  check-record : Record -> Result
  check-record r = check-op r (operator-of r)

  check-line : String -> Result
  check-line s with parse-record (ints-of-string s)
  ... | nothing = result false false false false false false false false false
  ... | just r = check-record r

-- ----------------------------------------------------------------------
-- * Accumulating the results

private
  record Acc : Set where
    constructor acc
    field
      n-total : ℕ
      n-lde n-exact n-k n-cs n-prkc n-norm n-bounds n-remark n-unit : ℕ
      msgs : List String
  open Acc

  acc0 : Acc
  acc0 = acc 0 0 0 0 0 0 0 0 0 0 []

  bump : Bool -> ℕ -> ℕ
  bump true k = k
  bump false k = suc k

  failure-text : ℕ -> Result -> String
  failure-text ix (result a b c d e f g h j) =
      "  line " Str.++ show (suc ix) Str.++ ":"
    Str.++ (if a then "" else " lde")
    Str.++ (if b then "" else " exact")
    Str.++ (if c then "" else " K-count")
    Str.++ (if d then "" else " CS-count")
    Str.++ (if e then "" else " prkc")
    Str.++ (if f then "" else " normal-form")
    Str.++ (if g then "" else " bounds")
    Str.++ (if h then "" else " remark-V11")
    Str.++ (if j then "" else " normal-form-unitary")

  add-result : ℕ -> Acc -> Result -> Acc
  add-result ix (acc t l x k s p q u v w ms) rs@(result a b c d e f g h j) =
    acc (suc t) (bump a l) (bump b x) (bump c k) (bump d s) (bump e p)
        (bump f q) (bump g u) (bump h v) (bump j w)
        (if (a ∧ b ∧ c ∧ d ∧ e ∧ f ∧ g ∧ h ∧ j) then ms
         else if List.length ms Nat.<ᵇ 10 then ms ++ (failure-text ix rs ∷ []) else ms)

  report : String -> ℕ -> ℕ -> String
  report name bad total =
    (if bad Nat.≡ᵇ 0 then "PASS " else "FAIL ") Str.++
    show (total ∸ bad) Str.++ "/" Str.++ show total Str.++ "  " Str.++ name

  -- Forcing. Without it the whole run is a 12000 deep chain of
  -- unevaluated thunks, each holding on to one matrix and one
  -- circuit, which exhausts the heap. Evaluating the sum of the
  -- counters after every record evaluates that record's five checks
  -- (ℕ addition is strict in both arguments in compiled code).
  acc-sum : Acc -> ℕ
  acc-sum (acc t l x k s p q u v w ms) =
    t Nat.+ l Nat.+ x Nat.+ k Nat.+ s Nat.+ p Nat.+ q Nat.+ u Nat.+ v Nat.+ w Nat.+ List.length ms

  force-io : ℕ -> IO {0ℓ} PU.⊤
  force-io zero = pure _
  force-io (suc n) = pure _

  n-bad : Acc -> ℕ
  n-bad (acc t l x k s p q u v w ms) =
    l Nat.+ x Nat.+ k Nat.+ s Nat.+ p Nat.+ q Nat.+ u Nat.+ v Nat.+ w

  progress : ℕ -> Acc -> String
  progress ix a = "... " Str.++ show ix Str.++ " records, " Str.++ show (n-bad a) Str.++ " failed checks"

  -- The main loop. The first argument counts down to the next
  -- progress report.
  loop : ℕ -> ℕ -> Acc -> List String -> IO Acc
  loop-step : ℕ -> ℕ -> List String -> Acc -> IO Acc

  loop cd ix a [] = pure a
  loop cd ix a (s ∷ ss) = loop-step cd (suc ix) ss (add-result ix a (check-line s))

  loop-step zero ix ss a = putStrLn (progress ix a) >> loop 999 ix a ss
  loop-step (suc cd) ix ss a = force-io (acc-sum a) >> loop cd ix a ss

-- ----------------------------------------------------------------------
-- * Main

private
  has-char : List Char -> Bool
  has-char [] = false
  has-char (_ ∷ _) = true

  nonempty : String -> Bool
  nonempty s = has-char (Str.toList s)

  select : List String -> List String -> List String
  select (p ∷ n ∷ _) ls = List.take (nat-of-string n) ls
  select _ ls = ls

  run-on : List String -> String -> IO Acc
  run-on args content = loop 999 0 acc0 (select args (List.filterᵇ nonempty (Str.lines content)))

  path-of : List String -> String
  path-of (p ∷ _) = p
  path-of [] = "experiment_data.dat"

  print-acc : Acc -> List String
  print-acc (acc t l x k s p q u v w ms) =
      ("records: " Str.++ show t)
    ∷ report "(a) lde U = recorded lde" l t
    ∷ report "(b) semantics of synth U = U (exact)" x t
    ∷ report "(c) kc (synth U) = recorded K-count" k t
    ∷ report "(d) csc (synth U) = recorded CS-count" s t
    ∷ report "(e) kc (synth U) = prkc U (Table II)" p t
    ∷ report "(f) refine gives the documented rho2 normal form" q t
    ∷ report "(g) csc <= kc+1, rlen <= 10 kc + 9 (Cor. V.8)" u t
    ∷ report "(h) lde-2 <= csc <= 2 lde + 1 (Remark V.11)" v t
    ∷ report "(i) refine gives a unitary rho2 normal form" w t
    ∷ ms

main : Main
main = run do
  args <- getArgs
  content <- readFiniteFile (path-of args)
  a <- run-on args content
  putStrLn (Str.unlines (print-acc a))
