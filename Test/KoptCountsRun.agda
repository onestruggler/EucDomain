-- The bounds of Section V of the paper, checked against the counts
-- recorded in the authors' data file (Kopt/Haskell/experiment_data.dat).
--
-- A record is ((l, M), c, gc, k, gk) where l is the lde, c and k are
-- the CS- and K-counts of the authors' algorithm (which Kopt.Synth
-- reproduces exactly, see Test.KoptSynthRun) and gc, gk are those of
-- Glaudell et al.'s algorithm. By Corollary V.8 k is the optimal
-- K-count kc(A), and by Section V B gc is the optimal CS-count cs(A).
-- We check
--
--   (1) c ≤ k + 1                      (Corollary V.8),
--   (2) gc ≤ k + 1                     (Theorem V.9, upper bound),
--   (3) k ≤ 2·gc + 2                   (Theorem V.9, lower bound
--                                       kc/2 - 1 ≤ cs),
--   (4) l - 2 ≤ gc ≤ 2l + 1            (Remark V.11),
--   (5) (k+1)(k-2) ≤ 2k·gc for k ≥ 3   (Corollary V.10,
--                                       (k+1)/cs ≤ 2 + 4/(k-2)),
--   (5') (k+1)(k-2) ≤ (2k+2)·gc         (Corollary V.10 with the
--                                       constant 6 instead of 4),
--   (6) k ≤ gk                         (our K-count is optimal),
--   (7) gc ≤ c                         (their CS-count is optimal),
--   (8) l - 2 ≤ c ≤ 2l + 1             (Remark V.11 for our counts).
--
-- No matrix arithmetic is involved, so this runs in a second.
--
-- Result on the authors' file: everything passes except (5), which
-- fails on 21 of the 12000 records. Those are exactly the records
-- where the lower bound of Theorem V.9 is tight, cs = k/2 - 1; then
-- (k+1)/cs = 2(k+1)/(k-2) = 2 + 6/(k-2) > 2 + 4/(k-2). Indeed
-- Corollary V.8 (ourCS ≤ k+1) together with Theorem V.9 only gives
-- (k+1)/cs ≤ 2 + 6/(k-2), which is (5') and which does hold for all
-- 12000 records.
--
-- Usage: agda-run.sh Test/KoptCountsRun.agda PATH [COUNT]

{-# OPTIONS --guardedness #-}

module Test.KoptCountsRun where

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

-- ----------------------------------------------------------------------
-- * Parsing (as in Test.KoptSynthRun, but only the five numbers)

private
  digit-val : Char -> ℕ
  digit-val c = Char.toℕ c ∸ 48

  read-nat : ℕ -> List Char -> ℕ × List Char
  read-nat a [] = a , []
  read-nat a (c ∷ cs) =
    if Char.isDigit c then read-nat (a Nat.* 10 Nat.+ digit-val c) cs else (a , c ∷ cs)

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

  -- (l , c , gc , k , gk)
  Counts : Set
  Counts = ℕ × ℕ × ℕ × ℕ × ℕ

  parse-counts : List ℤ -> Maybe Counts
  parse-counts xs with xs
  ... | [] = nothing
  ... | (l ∷ rest) with List.drop (List.length rest ∸ 4) rest
  ...   | (c ∷ gc ∷ k ∷ gk ∷ []) =
          just (Int.∣ l ∣ , Int.∣ c ∣ , Int.∣ gc ∣ , Int.∣ k ∣ , Int.∣ gk ∣)
  ...   | _ = nothing

-- ----------------------------------------------------------------------
-- * The bounds

private
  record Bad : Set where
    constructor bad
    field
      n-total b1 b2 b3 b4 b5 b5' b6 b7 b8 : ℕ
  open Bad

  bad0 : Bad
  bad0 = bad 0 0 0 0 0 0 0 0 0 0

  bump : Bool -> ℕ -> ℕ
  bump true k = k
  bump false k = suc k

  check-counts : Counts -> Bad -> Bad
  check-counts (l , c , gc , k , gk) (bad t a b d e f f' g h j) =
      bad (suc t) (bump o1 a) (bump o2 b) (bump o3 d) (bump o4 e)
          (bump o5 f) (bump o5' f') (bump o6 g) (bump o7 h) (bump o8 j)
    where
      o1 = c Nat.≤ᵇ suc k
      o2 = gc Nat.≤ᵇ suc k
      o3 = k Nat.≤ᵇ (2 Nat.* gc Nat.+ 2)
      o4 = ((l ∸ 2) Nat.≤ᵇ gc) ∧ (gc Nat.≤ᵇ suc (2 Nat.* l))
      o5 = if 3 Nat.≤ᵇ k then ((suc k Nat.* (k ∸ 2)) Nat.≤ᵇ (2 Nat.* k Nat.* gc)) else true
      o5' = if 3 Nat.≤ᵇ k then ((suc k Nat.* (k ∸ 2)) Nat.≤ᵇ ((2 Nat.* k Nat.+ 2) Nat.* gc)) else true
      o6 = k Nat.≤ᵇ gk
      o7 = gc Nat.≤ᵇ c
      o8 = ((l ∸ 2) Nat.≤ᵇ c) ∧ (c Nat.≤ᵇ suc (2 Nat.* l))

  check-line : String -> Bad -> Bad
  check-line s b with parse-counts (ints-of-string s)
  ... | nothing = b
  ... | just cs = check-counts cs b

  bad-sum : Bad -> ℕ
  bad-sum (bad t a b d e f f' g h j) =
    t Nat.+ a Nat.+ b Nat.+ d Nat.+ e Nat.+ f Nat.+ f' Nat.+ g Nat.+ h Nat.+ j

  force-io : ℕ -> IO {0ℓ} PU.⊤
  force-io zero = pure _
  force-io (suc n) = pure _

  loop : Bad -> List String -> IO Bad
  loop-step : List String -> Bad -> IO Bad

  loop b [] = pure b
  loop b (s ∷ ss) = loop-step ss (check-line s b)
  loop-step ss b = force-io (bad-sum b) >> loop b ss

  report : String -> ℕ -> ℕ -> String
  report name n total =
    (if n Nat.≡ᵇ 0 then "PASS " else "FAIL ") Str.++
    show (total ∸ n) Str.++ "/" Str.++ show total Str.++ "  " Str.++ name

  print-bad : Bad -> List String
  print-bad (bad t a b d e f f' g h j) =
      ("records: " Str.++ show t)
    ∷ report "(1) ourCS <= ourK + 1 (Cor. V.8)" a t
    ∷ report "(2) cs <= kc + 1 (Thm V.9, upper)" b t
    ∷ report "(3) kc/2 - 1 <= cs (Thm V.9, lower)" d t
    ∷ report "(4) lde-2 <= cs <= 2 lde + 1 (Remark V.11)" e t
    ∷ report "(5) (k+1)/cs <= 2 + 4/(k-2) for k >= 3 (Cor. V.10 as stated)" f t
    ∷ report "(5') (k+1)/cs <= 2 + 6/(k-2) for k >= 3 (Cor. V.10 amended)" f' t
    ∷ report "(6) ourK <= glaudellK (our K-count is optimal)" g t
    ∷ report "(7) glaudellCS <= ourCS (their CS-count is optimal)" h t
    ∷ report "(8) lde-2 <= ourCS <= 2 lde + 1" j t
    ∷ []

  has-char : List Char -> Bool
  has-char [] = false
  has-char (_ ∷ _) = true

  nonempty : String -> Bool
  nonempty s = has-char (Str.toList s)

  select : List String -> List String -> List String
  select (p ∷ n ∷ _) ls = List.take (nat-of-string n) ls
  select _ ls = ls

  path-of : List String -> String
  path-of (p ∷ _) = p
  path-of [] = "experiment_data.dat"

main : Main
main = run do
  args <- getArgs
  content <- readFiniteFile (path-of args)
  b <- loop bad0 (select args (List.filterᵇ nonempty (Str.lines content)))
  putStrLn (Str.unlines (print-bad b))
