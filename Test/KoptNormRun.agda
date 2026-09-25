-- Diagnostic: for which patterns and ldes does the refinement of
-- Section IV B fail to bring ρˡ₂(⟦L⟧·A·⟦R⟧) into the normal form
-- documented in the authors' Haskell code (Kopt.Patterns.normal-forms)?
--
-- Usage: agda-run.sh Test/KoptNormRun.agda PATH [COUNT]

{-# OPTIONS --guardedness #-}

module Test.KoptNormRun where

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
-- * Parsing (as in Test.KoptSynthRun)

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

  scale-from-whole : DComplex -> ZComplex -> DComplex
  scale-from-whole g z = from-whole z * g

  parse-line : List ℤ -> Maybe (Matrix 4 4 DComplex)
  parse-line ( l
             ∷ a₀ ∷ b₀ ∷ a₁ ∷ b₁ ∷ a₂ ∷ b₂ ∷ a₃ ∷ b₃
             ∷ c₀ ∷ d₀ ∷ c₁ ∷ d₁ ∷ c₂ ∷ d₂ ∷ c₃ ∷ d₃
             ∷ e₀ ∷ f₀ ∷ e₁ ∷ f₁ ∷ e₂ ∷ f₂ ∷ e₃ ∷ f₃
             ∷ g₀ ∷ h₀ ∷ g₁ ∷ h₁ ∷ g₂ ∷ h₂ ∷ g₃ ∷ h₃
             ∷ ourcs ∷ jcs ∷ ourk ∷ jk ∷ []) =
    just (matrix-map (scale-from-whole ((1/γ) ^ Int.∣ l ∣))
           (matrix4x4 (Cplx a₀ b₀ , Cplx a₁ b₁ , Cplx a₂ b₂ , Cplx a₃ b₃)
                      (Cplx c₀ d₀ , Cplx c₁ d₁ , Cplx c₂ d₂ , Cplx c₃ d₃)
                      (Cplx e₀ f₀ , Cplx e₁ f₁ , Cplx e₂ f₂ , Cplx e₃ f₃)
                      (Cplx g₀ h₀ , Cplx g₁ h₁ , Cplx g₂ h₂ , Cplx g₃ h₃)))
  parse-line _ = nothing

-- ----------------------------------------------------------------------
-- * The diagnostic

private
  show-r2-matrix : Matrix 4 4 R2 -> String
  show-r2-matrix m = showsPrec-Matrix (λ d r -> show-residue r) 0 m

  -- Failures per pattern.
  record Tally : Set where
    constructor tally
    field
      t-total t-bad : ℕ
      t-ii t-iii t-iv t-ivt t-v t-vi : ℕ
      t-msgs : List String
  open Tally

  tally0 : Tally
  tally0 = tally 0 0 0 0 0 0 0 0 []

  note : SixCases -> Tally -> Tally
  note II (tally a b c d e f g h ms) = tally a (suc b) (suc c) d e f g h ms
  note III (tally a b c d e f g h ms) = tally a (suc b) c (suc d) e f g h ms
  note IV (tally a b c d e f g h ms) = tally a (suc b) c d (suc e) f g h ms
  note IVt (tally a b c d e f g h ms) = tally a (suc b) c d e (suc f) g h ms
  note V (tally a b c d e f g h ms) = tally a (suc b) c d e f (suc g) h ms
  note VI (tally a b c d e f g h ms) = tally a (suc b) c d e f g (suc h) ms
  note I t = t

  add-msg : String -> Tally -> Tally
  add-msg s t@(tally a b c d e f g h ms) =
    if List.length ms Nat.<ᵇ 8 then tally a b c d e f g h (ms ++ (s ∷ [])) else t

  incr : Tally -> Tally
  incr (tally a b c d e f g h ms) = tally (suc a) b c d e f g h ms

  -- The actual ρˡ₂ after refinement, when it is not a normal form.
  report-bad : ℕ -> LevelData -> Matrix 4 4 DComplex -> Circuit × Circuit -> Tally -> Tally
  report-bad ix ld m (lcir , rcir) t =
    add-msg ("  line " Str.++ show (suc ix) Str.++ "  pattern " Str.++ show (lev-pat ld)
              Str.++ "  lde " Str.++ show (lev-lde ld) Str.++ "  rho2 = "
              Str.++ show-r2-matrix (residue-matrix (lev-lde ld) 2 (⟦ lcir ⟧ * m * ⟦ rcir ⟧)))
             (note (lev-pat ld) t)

  check : ℕ -> Matrix 4 4 DComplex -> Maybe LevelData -> Tally -> Tally
  check ix m nothing t = t
  check ix m (just ld) t =
    if refine-normal-form? m then incr t else incr (report-bad ix ld m (refine-at ld m) t)

  check-line : ℕ -> Tally -> String -> Tally
  check-line ix t s with parse-line (ints-of-string s)
  ... | nothing = t
  ... | just u = check ix u (level-of u) t

-- ----------------------------------------------------------------------
-- * Main

private
  tally-sum : Tally -> ℕ
  tally-sum (tally a b c d e f g h ms) =
    a Nat.+ b Nat.+ c Nat.+ d Nat.+ e Nat.+ f Nat.+ g Nat.+ h Nat.+ List.length ms

  force-io : ℕ -> IO {0ℓ} PU.⊤
  force-io zero = pure _
  force-io (suc n) = pure _

  loop : ℕ -> Tally -> List String -> IO Tally
  loop-step : ℕ -> List String -> Tally -> IO Tally

  loop ix t [] = pure t
  loop ix t (s ∷ ss) = loop-step (suc ix) ss (check-line ix t s)
  loop-step ix ss t = force-io (tally-sum t) >> loop ix t ss

  print-tally : Tally -> List String
  print-tally (tally a b c d e f g h ms) =
      ("records: " Str.++ show a Str.++ "   not in normal form: " Str.++ show b)
    ∷ ("by pattern:  II " Str.++ show c Str.++ "  III " Str.++ show d
        Str.++ "  IV " Str.++ show e Str.++ "  IVt " Str.++ show f
        Str.++ "  V " Str.++ show g Str.++ "  VI " Str.++ show h)
    ∷ ms

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
  t <- loop 0 tally0 (select args (List.filterᵇ nonempty (Str.lines content)))
  putStrLn (Str.unlines (print-tally t))
