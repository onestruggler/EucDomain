-- A diagnostic run over the authors' experimental data
-- (Kopt/Haskell/experiment_data.dat): for every operator of the file,
-- walk the complete path descent of Section IV B, and
--
--  * count how often each of the seven cases of Lemma IV.1 occurs
--    (this shows that all of them, including (iv)ᵀ and (v), are
--    exercised by the data);
--  * check that every step of the descent decreases prkc by exactly
--    the number of K gates it uses, which is Lemma IV.7 (Table II)
--    together with the transitions of Figure 1;
--  * check that every step either keeps the lde or decreases it by 1
--    (Lemma IV.4 and Figure 1);
--  * check that (iv), (iv)ᵀ, (v) and (vi) never occur at lde ≤ 1,
--    as claimed in Lemma IV.1.
--
-- Usage: agda-run.sh Test/KoptPatternsRun.agda PATH [COUNT]

{-# OPTIONS --guardedness #-}

module Test.KoptPatternsRun where

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

  operator-of : ℕ -> Matrix 4 4 ZComplex -> Matrix 4 4 DComplex
  operator-of l m = matrix-map (scale-from-whole ((1/γ) ^ l)) m

  parse-line : List ℤ -> Maybe (Matrix 4 4 DComplex)
  parse-line ( l
             ∷ a₀ ∷ b₀ ∷ a₁ ∷ b₁ ∷ a₂ ∷ b₂ ∷ a₃ ∷ b₃
             ∷ c₀ ∷ d₀ ∷ c₁ ∷ d₁ ∷ c₂ ∷ d₂ ∷ c₃ ∷ d₃
             ∷ e₀ ∷ f₀ ∷ e₁ ∷ f₁ ∷ e₂ ∷ f₂ ∷ e₃ ∷ f₃
             ∷ g₀ ∷ h₀ ∷ g₁ ∷ h₁ ∷ g₂ ∷ h₂ ∷ g₃ ∷ h₃
             ∷ ourcs ∷ jcs ∷ ourk ∷ jk ∷ []) =
    just (operator-of Int.∣ l ∣
           (matrix4x4 (Cplx a₀ b₀ , Cplx a₁ b₁ , Cplx a₂ b₂ , Cplx a₃ b₃)
                      (Cplx c₀ d₀ , Cplx c₁ d₁ , Cplx c₂ d₂ , Cplx c₃ d₃)
                      (Cplx e₀ f₀ , Cplx e₁ f₁ , Cplx e₂ f₂ , Cplx e₃ f₃)
                      (Cplx g₀ h₀ , Cplx g₁ h₁ , Cplx g₂ h₂ , Cplx g₃ h₃)))
  parse-line _ = nothing

-- ----------------------------------------------------------------------
-- * Walking the descent

private
  -- How often each of the seven cases occurs, and how many steps
  -- violated the invariants.
  record Walk : Set where
    constructor walk'
    field
      w-i w-ii w-iii w-iv w-ivt w-v w-vi : ℕ
      w-steps : ℕ
      w-bad-prkc : ℕ    -- steps that did not decrease prkc by their K-count
      w-bad-lde : ℕ     -- steps that changed the lde by something else than 0 or 1
      w-bad-none : ℕ    -- operators whose pattern could not be determined
      w-low : ℕ         -- occurrences of (iv), (iv)ᵀ, (v) or (vi) at lde ≤ 1
  open Walk

  walk0 : Walk
  walk0 = walk' 0 0 0 0 0 0 0 0 0 0 0 0

  count-case : SixCases -> Walk -> Walk
  count-case I (walk' a b c d e f g s p q r z) = walk' (suc a) b c d e f g s p q r z
  count-case II (walk' a b c d e f g s p q r z) = walk' a (suc b) c d e f g s p q r z
  count-case III (walk' a b c d e f g s p q r z) = walk' a b (suc c) d e f g s p q r z
  count-case IV (walk' a b c d e f g s p q r z) = walk' a b c (suc d) e f g s p q r z
  count-case IVt (walk' a b c d e f g s p q r z) = walk' a b c d (suc e) f g s p q r z
  count-case V (walk' a b c d e f g s p q r z) = walk' a b c d e (suc f) g s p q r z
  count-case VI (walk' a b c d e f g s p q r z) = walk' a b c d e f (suc g) s p q r z

  -- Lemma IV.1 claims that (iv), (iv)ᵀ, (v) and (vi) occur only when
  -- the lde is greater than 1.
  -- Called only for p ∈ {(iv), (iv)ᵀ, (v), (vi)}.
  count-low : SixCases -> ℕ -> Walk -> Walk
  count-low p l w@(walk' a b c d e f g s x q r z) =
    if l Nat.≤ᵇ 1 then walk' a b c d e f g s x q r (suc z) else w

  count-step : Bool -> Bool -> Walk -> Walk
  count-step okp okl (walk' a b c d e f g s p q r z) =
    walk' a b c d e f g (suc s) (if okp then p else suc p) (if okl then q else suc q) r z

  count-none : Walk -> Walk
  count-none (walk' a b c d e f g s p q r z) = walk' a b c d e f g s p q (suc r) z

  -- Lemma IV.7: one step of the descent decreases prkc by exactly the
  -- number of K gates it uses.
  prkc-step-ok : Matrix 4 4 DComplex -> Circuit -> Circuit -> Matrix 4 4 DComplex -> Bool
  prkc-step-ok m l₁ r₁ m' =
    prkc m Nat.≡ᵇ (kc (desugar-ck l₁) Nat.+ kc (desugar-ck r₁) Nat.+ prkc m')

  -- Lemma IV.4: one step keeps the lde or decreases it by one.
  lde-step-ok : Matrix 4 4 DComplex -> Matrix 4 4 DComplex -> Bool
  lde-step-ok m m' = (lde m' Nat.≡ᵇ lde m) ∨ (suc (lde m') Nat.≡ᵇ lde m)
    where
      _∨_ : Bool -> Bool -> Bool
      true ∨ _ = true
      false ∨ b = b

  walk : ℕ -> Matrix 4 4 DComplex -> Walk -> Walk
  walk-at : ℕ -> Matrix 4 4 DComplex -> Walk -> Maybe SixCases -> Walk
  walk-step : ℕ -> Matrix 4 4 DComplex -> Walk -> Circuit × Circuit -> Walk
  walk-next : ℕ -> Matrix 4 4 DComplex -> Walk -> Circuit -> Circuit -> Matrix 4 4 DComplex -> Walk

  walk zero m w = w
  walk (suc n) m w = walk-at n m w (patof m)

  walk-at n m w nothing = count-none w
  walk-at n m w (just I) = count-case I w
  walk-at n m w (just II) = walk-step n m (count-case II w) (decrease1-lde m)
  walk-at n m w (just III) = walk-step n m (count-case III w) (decrease1-lde m)
  walk-at n m w (just IV) = walk-step n m (count-low IV (lde m) (count-case IV w)) (decrease1-lde m)
  walk-at n m w (just IVt) = walk-step n m (count-low IVt (lde m) (count-case IVt w)) (decrease1-lde m)
  walk-at n m w (just V) = walk-step n m (count-low V (lde m) (count-case V w)) (decrease1-lde m)
  walk-at n m w (just VI) = walk-step n m (count-low VI (lde m) (count-case VI w)) (decrease1-lde m)

  walk-step n m w (l₁ , r₁) = walk-next n m w l₁ r₁ (⟦ l₁ ⟧ * m * ⟦ r₁ ⟧)

  walk-next n m w l₁ r₁ m' =
    walk n m' (count-step (prkc-step-ok m l₁ r₁ m') (lde-step-ok m m') w)

  walk-line : Walk -> String -> Walk
  walk-line w s with parse-line (ints-of-string s)
  ... | nothing = count-none w
  ... | just u = walk (suc (2 Nat.* lde u)) u w

-- ----------------------------------------------------------------------
-- * Main

private
  walk-sum : Walk -> ℕ
  walk-sum (walk' a b c d e f g s p q r z) =
    a Nat.+ b Nat.+ c Nat.+ d Nat.+ e Nat.+ f Nat.+ g Nat.+ s Nat.+ p Nat.+ q Nat.+ r Nat.+ z

  force-io : ℕ -> IO {0ℓ} PU.⊤
  force-io zero = pure _
  force-io (suc n) = pure _

  loop : Walk -> List String -> IO Walk
  loop-step : List String -> Walk -> IO Walk

  loop w [] = pure w
  loop w (s ∷ ss) = loop-step ss (walk-line w s)
  loop-step ss w = force-io (walk-sum w) >> loop w ss

  print-walk : Walk -> List String
  print-walk (walk' a b c d e f g s p q r z) =
      ("cases on the descents:  I " Str.++ show a
        Str.++ "  II " Str.++ show b Str.++ "  III " Str.++ show c
        Str.++ "  IV " Str.++ show d Str.++ "  IVt " Str.++ show e
        Str.++ "  V " Str.++ show f Str.++ "  VI " Str.++ show g)
    ∷ ("steps: " Str.++ show s)
    ∷ ((if p Nat.≡ᵇ 0 then "PASS " else "FAIL ") Str.++ show (s ∸ p) Str.++ "/" Str.++ show s
        Str.++ "  every step decreases prkc by its K-count (Lemma IV.7)")
    ∷ ((if q Nat.≡ᵇ 0 then "PASS " else "FAIL ") Str.++ show (s ∸ q) Str.++ "/" Str.++ show s
        Str.++ "  every step keeps the lde or lowers it by 1 (Lemma IV.4)")
    ∷ ((if z Nat.≡ᵇ 0 then "PASS " else "FAIL ") Str.++ show z
        Str.++ "  occurrences of (iv), (iv)t, (v), (vi) at lde <= 1 (Lemma IV.1)")
    ∷ ("operators without a pattern: " Str.++ show r)
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
  w <- loop walk0 (select args (List.filterᵇ nonempty (Str.lines content)))
  putStrLn (Str.unlines (print-walk w))
