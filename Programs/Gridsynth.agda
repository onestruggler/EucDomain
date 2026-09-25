-- This module is an Agda port of the gridsynth command line program
-- of the Haskell package newsynth (programs/gridsynth.hs): a command
-- line interface to the single-qubit approximate synthesis algorithm
-- (Quantum.Synthesis.GridSynth).
--
-- Build and run with (from the repository root):
--
--   agda --compile Programs/Gridsynth.agda    (the executable is Gridsynth)
--   ./Gridsynth pi/128 -d 10 -r 1
--
-- All options, output formats and error messages are those of the
-- Haskell program; with the same random seed (-r), the output is
-- identical, except for the measured run times (Runtime and
-- Time/candidate of -s, and the timing lines of -t).
--
-- Differences from Haskell:
--
-- * Without -r, Haskell uses newStdGen, which splits a global
--   generator initialized from the clock (random-1.1: mkStdGen of
--   seconds⋅12345 + picoseconds + CPU time). This port does the same
--   computation: it reads the POSIX time and the CPU time once, forms
--   the generator from them, and uses the second half of its split.
--   The seeds are thus random, but of course not those Haskell would
--   pick.
--
-- * The -r seed is parsed exactly like Haskell's "reads s :: StdGen"
--   (random-1.1): either two decimal numbers "s1 s2" (possibly
--   surrounded by white space, nothing after them), each wrapped to a
--   32-bit Int like Haskell's Int32 arithmetic, or, if that fails,
--   any string of at most 6 characters, which is hashed with
--   mkStdGen. (Seeds outside the range of random-1.1's generators,
--   e.g. negative ones after wrapping, give the same printed seed but
--   the generator arithmetic may differ, since the Agda StdGen uses
--   unbounded integers.)
--
-- * Numbers (-d, -b, -e, -f, -c) are parsed like Haskell's "reads" (see
--   Programs.CommandLine). The number of digits must be finite: for
--   -d Infinity (which Haskell accepts, and then loops forever) the
--   exponent printed is 0 and the search runs with an infinite
--   precision request, i.e. does not terminate either.
--
-- * The timings use the POSIX clock (Haskell: getCurrentTime), and are
--   printed like Haskell's NominalDiffTime (picoseconds, trailing zeros
--   removed).
--
-- * The table mode (-t) is ported in full.

{-# OPTIONS --guardedness #-}

module Programs.Gridsynth where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
import Data.Nat.Show as NatS
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Integer.DivMod as IntD
open import Data.Float.Base as Float using (Float)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String ; _++_)
open import Data.Unit.Polymorphic.Base using () renaming (⊤ to ⊤ᵖ ; tt to ttᵖ)
open import Function.Base using (_∘_)
open import IO
import IO.Primitive.Core as Prim
open import System.Environment using (getArgs)
open import System.Exit using (exitSuccess ; exitFailure)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix hiding (Times)
open import Quantum.Synthesis.CliffordT
open import Quantum.Synthesis.SymReal
open import Quantum.Synthesis.LaTeX
open import Quantum.Synthesis.Random using (StdGen ; StdGen' ; mkStdGen ; readStdGen ; split ; randomR)
open import Quantum.Synthesis.GridSynth
open import Data.Number.FixedPrec using (float-ceiling)

open import Programs.GetOpt
open import Programs.CommandLine

-- ----------------------------------------------------------------------
-- * Clock

postulate
  -- The current POSIX time, in picoseconds.
  primGetPicoTime : Prim.IO ℕ
  -- The CPU time used by the program, in picoseconds.
  primGetCPUTime : Prim.IO ℕ

{-# FOREIGN GHC import qualified Data.Time.Clock.POSIX #-}
{-# FOREIGN GHC import qualified System.CPUTime #-}
{-# COMPILE GHC primGetPicoTime = fmap (\ t -> truncate (toRational t * 1000000000000)) Data.Time.Clock.POSIX.getPOSIXTime #-}
{-# COMPILE GHC primGetCPUTime = System.CPUTime.getCPUTime #-}

getPicoTime : IO ℕ
getPicoTime = lift primGetPicoTime

getCPUTime : IO ℕ
getCPUTime = lift primGetCPUTime

private
  pico : ℕ
  pico = 1000000000000

  divN modN : ℕ -> ℕ -> ℕ
  divN a zero = 0
  divN a (suc b) = a Nat./ suc b
  modN a zero = a
  modN a (suc b) = a Nat.% suc b

-- Show a time difference (in picoseconds) like Haskell's show for
-- NominalDiffTime, e.g. "0.020797535s".
show-time : ℕ -> String
show-time ps = NatS.show (divN ps pico) ++ with-dot (frac (modN ps pico)) ++ "s"
  where
    chop : ℕ -> ℕ -> String
    chop zero n = NatS.show n
    chop (suc f) n = if modN n 10 Nat.≡ᵇ 0 then chop f (divN n 10) else NatS.show n
    frac : ℕ -> String
    frac zero = ""
    frac d@(suc _) = String.fromList (List.replicate (12 Nat.∸ String.length (NatS.show d)) '0') ++ chop 12 d
    with-dot : String -> String
    with-dot "" = ""
    with-dot s = "." ++ s

-- The picoseconds as a Float (Haskell: fromRational (toRational secs)).
time-to-float : ℕ -> Float
time-to-float ps = Float.fromRatio (+ ps) (+ pico)

-- ----------------------------------------------------------------------
-- * Option processing

-- A data type to hold values set by command line options.
record Options : Set where
  field
    -- Requested precision in decimal digits (default: 10).
    opt-digits : Maybe Float
    -- The angle θ to approximate.
    opt-theta : Maybe SymReal
    -- Decompose up to a global phase?
    opt-phase : Bool
    -- The amount of "effort" to spend on factoring.
    opt-effort : ℕ
    -- Output operator in hex coding? (default: ASCII).
    opt-hex : Bool
    -- Output statistics?
    opt-stats : Bool
    -- Use LaTeX format?
    opt-latex : Bool
    -- Generate the table of results for the paper?
    opt-table : Bool
    -- Repeat count for --table mode (default: 50).
    opt-count : Maybe ℕ
    -- An optional random seed.
    opt-rseed : Maybe StdGen
open Options

-- The initial default options.
defaultOptions : Options
defaultOptions = record
  { opt-digits = nothing
  ; opt-theta = nothing
  ; opt-phase = false
  ; opt-effort = 25
  ; opt-hex = false
  ; opt-stats = false
  ; opt-latex = false
  ; opt-table = false
  ; opt-count = nothing
  ; opt-rseed = nothing
  }

private
  -- Wrap an integer to Haskell's Int32 range.
  to-int32 : ℤ -> ℤ
  to-int32 n = + ((n Int.+ + 2147483648) IntD.%ℕ 4294967296) Int.- + 2147483648

  -- readDec after skipping white space: a decimal number and the rest.
  readDec : List Char -> Maybe (ℕ × List Char)
  readDec cs = go (List.dropWhileᵇ Char.isSpace cs) nothing
    where
      go : List Char -> Maybe ℕ -> Maybe (ℕ × List Char)
      go [] nothing = nothing
      go [] (just n) = just (n , [])
      go (c ∷ cs) acc with Char.isDigit c | acc
      ... | true | nothing = go cs (just (Char.toℕ c Nat.∸ 48))
      ... | true | just n = go cs (just (n Nat.* 10 Nat.+ (Char.toℕ c Nat.∸ 48)))
      ... | false | nothing = nothing
      ... | false | just n = just (n , c ∷ cs)

  try-read : List Char -> Maybe (ℕ × ℕ × List Char)
  try-read cs with readDec cs
  ... | nothing = nothing
  ... | just (a , r1) with readDec r1
  ...   | nothing = nothing
  ...   | just (b , r2) = just (a , b , r2)

-- Parse a random seed like Haskell's "reads s :: StdGen" (random-1.1),
-- accepting only complete parses.
parse-rseed : String -> Maybe StdGen
parse-rseed s with try-read (String.toList s)
... | just (a , b , []) = just (StdGen' (to-int32 (+ a)) (to-int32 (+ b)))
... | just (_ , _ , _ ∷ _) = nothing
... | nothing = if String.length s Nat.≤ᵇ 6 then just (readStdGen s) else nothing

-- The list of command line options, in the format required by getOpt.
-- The argument is the action that prints the usage info.
options-with : IO {0ℓ} ⊤ᵖ -> List (OptDescr (Options -> IO Options))
options-with usage =
  Option' ('h' ∷ []) ("help" ∷ []) (NoArg help) "print usage info and exit" ∷
  Option' ('d' ∷ []) ("digits" ∷ []) (ReqArg digits "<n>") "set precision in decimal digits (default: 10)" ∷
  Option' ('b' ∷ []) ("bits" ∷ []) (ReqArg bits "<n>") "set precision in bits" ∷
  Option' ('e' ∷ []) ("epsilon" ∷ []) (ReqArg epsilon "<n>") "set precision as epsilon (default: 1e-10)" ∷
  Option' ('p' ∷ []) ("phase" ∷ []) (NoArg phase) "decompose up to a global phase (default: no)" ∷
  Option' ('f' ∷ []) ("effort" ∷ []) (ReqArg effort "\"<n>\"") "how hard to try to factor (default: 25)" ∷
  Option' ('x' ∷ []) ("hex" ∷ []) (NoArg hex) "output hexadecimal coding (default: ASCII)" ∷
  Option' ('s' ∷ []) ("stats" ∷ []) (NoArg stats) "output statistics" ∷
  Option' ('l' ∷ []) ("latex" ∷ []) (NoArg latex) "use LaTeX output format" ∷
  Option' ('t' ∷ []) ("table" ∷ []) (NoArg table) "generate the table of results for the article" ∷
  Option' ('c' ∷ []) ("count" ∷ []) (ReqArg count "<n>") "repeat count for --table mode (default: 50)" ∷
  Option' ('r' ∷ []) ("rseed" ∷ []) (ReqArg rseed "\"<s>\"") "set optional random seed (default: random)" ∷
  []
  where
    help : Options -> IO Options
    help o = do
      usage
      exitSuccess

    digits : String -> Options -> IO Options
    digits string o with parse-double string
    ... | just n = if 0.0 Float.≤ᵇ n then pure (record o { opt-digits = just n })
                   else optfail ("Number of digits must not be negative -- " ++ string ++ "\n")
    ... | nothing = optfail ("Invalid digits -- " ++ string ++ "\n")

    bits : String -> Options -> IO Options
    bits string o with parse-double string
    ... | just n = if 0.0 Float.≤ᵇ n then pure (record o { opt-digits = just (n Float.* logBase 10.0 2.0) })
                   else optfail ("Number of bits must not be negative -- " ++ string ++ "\n")
    ... | nothing = optfail ("Invalid bits -- " ++ string ++ "\n")

    epsilon : String -> Options -> IO Options
    epsilon string o with parse-double string
    ... | just eps = if (eps Float.<ᵇ 1.0) ∧ (0.0 Float.<ᵇ eps)
                     then pure (record o { opt-digits = just (Float.- (logBase 10.0 eps)) })
                     else optfail ("Epsilon must be between 0 and 1 -- " ++ string ++ "\n")
    ... | nothing = optfail ("Invalid epsilon -- " ++ string ++ "\n")

    phase : Options -> IO Options
    phase o = pure (record o { opt-phase = true })

    effort : String -> Options -> IO Options
    effort string o with parse-int string
    ... | just e with to-int64 e
    ...   | + (suc e') = pure (record o { opt-effort = suc e' })
    ...   | _ = optfail ("Effort must be positive -- " ++ string ++ "\n")
    effort string o | nothing = optfail ("Invalid effort -- " ++ string ++ "\n")

    hex : Options -> IO Options
    hex o = pure (record o { opt-hex = true })

    stats : Options -> IO Options
    stats o = pure (record o { opt-stats = true })

    latex : Options -> IO Options
    latex o = pure (record o { opt-latex = true })

    table : Options -> IO Options
    table o = pure (record o { opt-table = true })

    count : String -> Options -> IO Options
    count string o with parse-int string
    ... | just n with to-int64 n
    ...   | + (suc n') = pure (record o { opt-count = just (suc n') })
    ...   | _ = optfail ("Invalid count, must be positive -- " ++ string ++ "\n")
    count string o | nothing = optfail ("Invalid count -- " ++ string ++ "\n")

    rseed : String -> Options -> IO Options
    rseed string o with parse-rseed string
    ... | just g = pure (record o { opt-rseed = just g })
    ... | nothing = optfail ("Invalid random seed -- " ++ string ++ "\n")

-- The usage message.
usage-header : String
usage-header =
  "Usage: gridsynth [OPTION...] <theta>\n" ++
  "Arguments:\n" ++
  " <theta>                   z-rotation angle. May be symbolic, e.g. pi/128\n" ++
  "Options:"

-- Print usage message to stdout.
usage : IO {0ℓ} ⊤ᵖ
usage = putStr (usageInfo usage-header (options-with (pure ttᵖ)))

options : List (OptDescr (Options -> IO Options))
options = options-with usage

private
  foldM : {A : Set₁} {B : Set} -> (B -> A -> IO B) -> B -> List A -> IO B
  foldM f b [] = pure b
  foldM f b (x ∷ xs) = f b x >>= λ b' -> foldM f b' xs

  -- The parsed command line, given the result of getOpt. It is taken as
  -- an ARGUMENT and not scrutinised with "with": a with-abstraction
  -- normalises its scrutinee, i.e. the whole concrete option table
  -- "options", which cost 4.3 s of type-checking time.
  dopts-of : List (Options -> IO Options) × List String × List String -> IO Options
  dopts-of (o , args , errs) = do
    opts <- foldM (λ opts f -> f opts) defaultOptions o
    check-errs errs
    process-args opts args
    where
      check-errs : List String -> IO {0ℓ} ⊤ᵖ
      check-errs [] = pure ttᵖ
      check-errs es@(_ ∷ _) = optfail (String.concat es)

      process-args : Options -> List String -> IO Options
      process-args opts [] = pure opts
      process-args opts (string ∷ []) with parse-SymReal string
      ... | just theta = pure (record opts { opt-theta = just theta })
      ... | nothing = optfail ("Invalid theta -- " ++ string ++ "\n")
      process-args opts (h1 ∷ h2 ∷ []) = optfail ("Too many non-option arguments -- " ++ h1 ++ ", " ++ h2 ++ "\n")
      process-args opts (h1 ∷ h2 ∷ _ ∷ _) = optfail ("Too many non-option arguments -- " ++ h1 ++ ", " ++ h2 ++ "...\n")

-- Process argv-style command line options into an Options structure.
dopts : List String -> IO Options
dopts argv = dopts-of (getOpt Permute options argv)

-- ----------------------------------------------------------------------
-- * Miscellaneous

private
  -- Haskell's round at Double (round half to even), as an integer.
  round-float : Float -> ℤ
  round-float x = go (float-floor x)
    where
      float-floor : Float -> ℤ
      float-floor y with Float.⌊ y ⌋
      ... | just n = n
      ... | nothing = + 0
      even-z : ℤ -> Bool
      even-z n = Int.∣ n ∣ Nat.% 2 Nat.≡ᵇ 0
      go : ℤ -> ℤ
      go r = if 0.5 Float.<ᵇ d then r Int.+ + 1
             else if d Float.<ᵇ 0.5 then r
             else if even-z r then r else r Int.+ + 1
        where d = x Float.- Float.fromℤ r

  pow10f : ℕ -> Float
  pow10f n = Float.fromℕ (10 Nat.^ n)

-- Round a Float to the given number of decimals.
round-to : ℕ -> Float -> Float
round-to n x = Float.fromℤ (round-float (x Float.* pow10f n)) Float.÷ pow10f n

private
  exp-value : ℕ -> ℤ -> Maybe Float -> Float
  exp-value d n nothing = 0.0
  exp-value d n (just x) = round-to d (10.0 Float.** (Float.fromℤ n Float.- x))

-- Show the number 10^(-x) in the format 10^(-n) or 1.23*10^(-n), with
-- precision d and exponent -n. A value of nothing is treated as 0.
--
-- For example, display 0.316*10^(-13) instead of 10^(-13.5).
show-exp : ℕ -> ℤ -> Maybe Float -> String
show-exp d n x = mk (exp-value d n x)
  where
    mk : Float -> String
    mk y = if y Float.≡ᵇ 1.0 then "10^(" ++ show (Int.- n) ++ ")"
           else show-ffloat d y ++ "*10^(" ++ show (Int.- n) ++ ")"

-- Show the number 10^(-x) in the format 10^{-n} or 1.23\cdot 10^{-n},
-- with precision d and exponent -n. A value of nothing is treated as
-- 0.
showlatex-exp : ℕ -> ℤ -> Maybe Float -> String
showlatex-exp d n x = mk (exp-value d n x)
  where
    mk : Float -> String
    mk y = if y Float.≡ᵇ 1.0 then "10^{" ++ show (Int.- n) ++ "}"
           else show-ffloat d y ++ "\\cdot 10^{" ++ show (Int.- n) ++ "}"

-- Either show or showlatex, depending on boolean flag.
showf : {A : Set} {{_ : Show A}} {{_ : ShowLaTeX A}} -> Bool -> A -> String
showf true = showlatex
showf false = show

-- Either show-exp or showlatex-exp, depending on boolean flag.
showf-exp : Bool -> ℕ -> ℤ -> Maybe Float -> String
showf-exp true = showlatex-exp
showf-exp false = show-exp

-- Expand a random seed g into a list of n random seeds (Haskell: an
-- infinite list).
expand-seed : ℕ -> StdGen -> List StdGen
expand-seed zero g = []
expand-seed (suc n) g with split g
... | g1 , g2 = g1 ∷ expand-seed n g2

-- Output the given string, right-padded to n characters using spaces.
putStrPad : ℕ -> String -> IO {0ℓ} ⊤ᵖ
putStrPad n s = putStr (s ++ String.fromList (List.replicate (n Nat.∸ String.length s) ' '))

-- Strip global phase gates from a word.
strip-phases : List Gate -> List Gate
strip-phases [] = []
strip-phases (W ∷ xs) = strip-phases xs
strip-phases (x ∷ xs) = x ∷ strip-phases xs

private
  is-T : Gate -> Bool
  is-T T = true
  is-T _ = false

  count-T : List Gate -> ℕ
  count-T gs = List.length (List.filterᵇ is-T gs)

  is-fail : DStatus -> Bool
  is-fail Fail = true
  is-fail _ = false

  is-timeout : DStatus -> Bool
  is-timeout Timeout = true
  is-timeout _ = false

  is-success : DStatus -> Bool
  is-success Success = true
  is-success _ = false

  count-status : (DStatus -> Bool) -> CandidateInfo -> ℕ
  count-status p cinfo = List.length (List.filterᵇ (λ { (_ , _ , st) -> p st }) cinfo)

  -- last [ tcount | (u, tcount, status) <- cinfo, status /= Fail ]
  -- (0 if there is no such candidate, which cannot happen).
  lower-bound : CandidateInfo -> ℕ
  lower-bound cinfo = List.foldl (λ acc x -> sel acc x) 0 cinfo
    where
      sel : ℕ -> DOmega × ℕ × DStatus -> ℕ
      sel acc (_ , tc , st) = if is-fail st then acc else tc

  candidates-line : String -> CandidateInfo -> String
  candidates-line prefix cinfo =
    prefix ++ "Candidates tried: " ++ show (List.length cinfo) ++ " ("
    ++ show (count-status is-fail cinfo) ++ " failed, "
    ++ show (count-status is-timeout cinfo) ++ " timed out, "
    ++ show (count-status is-success cinfo) ++ " succeeded)"

  -- Convert log₀.₅ of the error to log₀.₁.
  err-to-decimal : Maybe Float -> Maybe Float
  err-to-decimal nothing = nothing
  err-to-decimal (just x) = just (x Float.* logBase 10.0 2.0)

  null : {A : Set} -> List A -> Bool
  null [] = true
  null (_ ∷ _) = false

  show-hex : ℕ -> String
  show-hex n = String.fromList (go n n [])
    where
      hexdigit : ℕ -> Char
      hexdigit d = if d Nat.<ᵇ 10 then Char.fromℕ (48 Nat.+ d) else Char.fromℕ (87 Nat.+ d)
      -- the first argument is fuel.
      go : ℕ -> ℕ -> List Char -> List Char
      go _ zero [] = '0' ∷ []
      go _ zero acc@(_ ∷ _) = acc
      go zero _ acc = acc
      go (suc f) m@(suc _) acc = go f (divN m 16) (hexdigit (modN m 16) ∷ acc)

  gridsynth-fun : Bool -> StdGen -> Float -> SymReal -> ℕ -> GridSynthResult
  gridsynth-fun false = gridsynth-stats
  gridsynth-fun true = gridsynth-phase-stats

  -- Haskell's newStdGen (see the header).
  newStdGen : IO StdGen
  newStdGen = do
    t <- getPicoTime
    c <- getCPUTime
    pure (proj₂ (split (mkStdGen (+ (divN t pico Nat.* 12345 Nat.+ modN t pico Nat.+ c)))))

  get-seed : Maybe StdGen -> IO StdGen
  get-seed nothing = newStdGen
  get-seed (just g) = pure g

-- ----------------------------------------------------------------------
-- * The main function

-- ----------------------------------------------------------------------
-- ** Default main

private
  -- The output and the statistics, given the result of gridsynth.
  -- (The list of gates is passed as an argument, so that it is
  -- computed only once; where-bound values are not shared.)
  main-default-gates : Options -> StdGen -> SymReal -> Float -> ℤ -> GridSynthResult -> List Gate -> IO {0ℓ} ⊤ᵖ
  main-default-gates options g theta digits exponent r gates = do
    t0 <- getPicoTime
    putStrLn output
    t1 <- getPicoTime
    stats-lines (t1 Nat.∸ t0)
    where
      -- (projections instead of a pattern, so that the computation
      -- happens lazily during the output, and is timed, as in Haskell)
      m : U2 DOmega
      m = proj₁ r
      err : Maybe Float
      err = proj₁ (proj₂ r)
      cinfo : CandidateInfo
      cinfo = proj₂ (proj₂ r)

      l = opt-latex options

      output : String
      output =
        if opt-hex options then show-hex Int.∣ convert {List Gate} {ℤ} gates ∣
        else if l then (if null gates then "I" else showlatex gates)
        else (if null gates then "I" else convert {List Gate} {String} gates)

      err-d : Maybe Float
      err-d = err-to-decimal err

      stats-lines : ℕ -> IO {0ℓ} ⊤ᵖ
      stats-lines secs =
        if not (opt-stats options) then pure ttᵖ
        else do
          putStrLn ("Random seed: " ++ show g)
          putStrLn ("T-count: " ++ show (count-T gates))
          putStrLn ("Lower bound on T-count: " ++ show (lower-bound cinfo))
          putStrLn ("Theta: " ++ showf l theta)
          putStrLn ("Epsilon: " ++ showf-exp l 10 exponent (just digits))
          putStrLn ("Matrix: " ++ showf l m)
          putStrLn ("Actual error: " ++ showf-exp l 10 exponent err-d)
          putStrLn ("Runtime: " ++ show-time secs)
          putStrLn (candidates-line "" cinfo)
          putStrLn ("Time/candidate: " ++ show-time (divN secs (List.length cinfo)))

  main-default-output : Options -> StdGen -> SymReal -> Float -> ℤ -> GridSynthResult -> IO {0ℓ} ⊤ᵖ
  main-default-output options g theta digits exponent r =
    main-default-gates options g theta digits exponent r
      (if opt-phase options then strip-phases (to-gates (proj₁ r)) else to-gates (proj₁ r))

-- The default task for the main function: synthesize one angle, for
-- one given precision, possibly with outputting some statistics.
main-default : Options -> IO {0ℓ} ⊤ᵖ
main-default options = do
  theta <- get-theta (opt-theta options)
  check-count (opt-count options)
  g <- get-seed (opt-rseed options)
  -- The payload is computed lazily, during the output (timed there).
  main-default-output options g theta digits (float-ceiling digits)
    (gridsynth-fun (opt-phase options) g (digits Float.* logBase 2.0 10.0) theta (opt-effort options))
  where
    digits : Float
    digits with opt-digits options
    ... | nothing = 10.0
    ... | just d = d

    get-theta : Maybe SymReal -> IO SymReal
    get-theta nothing = optfail "Missing argument: theta.\n"
    get-theta (just t) = pure t

    check-count : Maybe ℕ -> IO {0ℓ} ⊤ᵖ
    check-count nothing = pure ttᵖ
    check-count (just _) = optfail "Option -c is only supported with --table.\n"

-- ----------------------------------------------------------------------
-- ** Generate output in LaTeX table format

-- The result of one_run: the approximating operator U, the
-- approximating circuit, log₀.₅ of the actual approximation error (or
-- nothing if the error is 0), the number of candidates tried, the
-- T-count of U, the computed lower bound for the T-count, and the
-- runtime in seconds.
RunResult : Set
RunResult = U2 DOmega × List Gate × Maybe Float × ℕ × ℕ × ℕ × Float

private
  float-floor : Float -> ℤ
  float-floor y with Float.⌊ y ⌋
  ... | just n = n
  ... | nothing = + 0

  one-run-circ : StdGen -> SymReal -> Float -> GridSynthResult -> List Gate -> IO RunResult
  one-run-circ g theta prec-d r circ = do
    t0 <- getPicoTime
    putStrLn ("% T-count: " ++ show tcount)
    t1 <- getPicoTime
    rest (t1 Nat.∸ t0)
    where
      op : U2 DOmega
      op = proj₁ r
      err : Maybe Float
      err = proj₁ (proj₂ r)
      cinfo : CandidateInfo
      cinfo = proj₂ (proj₂ r)
      exponent = float-floor prec-d
      tcount : ℕ
      tcount = count-T circ
      ct : ℕ
      ct = List.length cinfo
      tlower : ℕ
      tlower = lower-bound cinfo
      u t : DOmega
      u = proj₁ (proj₁ (from-matrix2x2 op))
      t = proj₁ (proj₂ (from-matrix2x2 op))
      err-d : Maybe Float
      err-d = err-to-decimal err

      rest : ℕ -> IO RunResult
      rest secs = do
        putStrLn ("% Lower bound on T-count: " ++ show tlower)
        putStrLn ("% Circuit: " ++ (if null circ then "I" else convert {List Gate} {String} circ))
        putStrLn ("% u: " ++ showlatex u)
        putStrLn ("% t: " ++ showlatex t)
        putStrLn ("% Actual error: " ++ show-exp 10 exponent err-d)
        putStrLn ("% Runtime: " ++ show-time secs)
        putStrLn (candidates-line "% " cinfo)
        putStrLn ("% Time/candidate: " ++ show-time (divN secs ct))
        putStrLn ""
        hFlush stdout
        pure (op , circ , err , ct , tcount , tlower , time-to-float secs)

  one-run-output : StdGen -> SymReal -> Float -> GridSynthResult -> IO RunResult
  one-run-output g theta prec-d r = one-run-circ g theta prec-d r (synthesis-u2 (proj₁ r))

-- Run one instance of the algorithm, using the given θ, and measuring
-- various things including the running time. Note: here, the
-- precision is expressed in decimal, not binary, digits.
--
-- The inputs are, respectively: a source of randomness, the angle θ,
-- the precision in decimal digits, an amount of effort to spend on
-- factoring, and a boolean flag determining whether we should
-- decompose up to a global phase.
one-run : StdGen -> SymReal -> Float -> ℕ -> Bool -> IO RunResult
one-run g theta prec-d effort phase = do
  putStrLn ("% Epsilon: " ++ show-exp 10 (float-floor prec-d) (just prec-d))
  putStrLn ("% Theta: " ++ show theta)
  putStrLn ("% Random seed: " ++ show g)
  one-run-output g theta prec-d (gridsynth-fun phase g (prec-d Float.* logBase 2.0 10.0) theta effort)

private
  sequenceIO : {A : Set} -> List (IO A) -> IO (List A)
  sequenceIO [] = pure []
  sequenceIO (x ∷ xs) = x >>= λ a -> sequenceIO xs >>= λ as -> pure (a ∷ as)

  sequenceIO′ : {A : Set} -> List (IO A) -> IO {0ℓ} ⊤ᵖ
  sequenceIO′ [] = pure ttᵖ
  sequenceIO′ (x ∷ xs) = x >> sequenceIO′ xs

  many-runs-output : ℕ -> Float -> List RunResult -> IO {0ℓ} ⊤ᵖ
  many-runs-output n prec-d [] = pure ttᵖ
  many-runs-output n prec-d results@((_ , _ , err , _ , tcount , tlower , _) ∷ _) = do
    putStrPad 30 (showlatex-exp 5 exponent (just prec-d) ++ " &")
    putStrLn "% Epsilon"
    putStrPad 30 (show tcount ++ " &")
    putStrLn "% T-count"
    putStrPad 30 ("\\geq " ++ show tlower ++ " &")
    putStrLn "% Lower bound on T-count"
    putStrPad 30 (showlatex-exp 5 exponent err-d ++ " &")
    putStrLn "% Actual error"
    putStrPad 30 (show-ffloat 4 avg-time ++ "s" ++ " &")
    putStrLn ("% Runtime, averaged over " ++ show n ++ " runs")
    putStrPad 30 (show-ffloat 1 avg-candidates ++ " &")
    putStrLn ("% Candidates tried, averaged over " ++ show n ++ " runs")
    putStrPad 30 (show-ffloat 4 time-per-candidate ++ "s" ++ " \\\\")
    putStrLn ("% Time per candidate, averaged over " ++ show n ++ " runs")
    putStrLn ""
    putStrLn "% ----------------------------------------------------------------------"
    putStrLn ""
    hFlush stdout
    where
      total-time : Float
      total-time = List.foldl (λ acc r -> acc Float.+ proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))) 0.0 results
      total-candidates : ℕ
      total-candidates = List.foldl (λ acc r -> acc Nat.+ proj₁ (proj₂ (proj₂ (proj₂ r)))) 0 results
      avg-time = total-time Float.÷ Float.fromℕ n
      avg-candidates = Float.fromℕ total-candidates Float.÷ Float.fromℕ n
      time-per-candidate = total-time Float.÷ Float.fromℕ total-candidates
      err-d : Maybe Float
      err-d = err-to-decimal err
      exponent = float-floor prec-d

-- Repeat the algorithm n times with the same parameters but random
-- angles, to average things like running time. The inputs are,
-- respectively: a source of randomness, a repeat count, the precision
-- in decimal digits, an amount of effort to spend on factoring, and a
-- flag that determines whether to factor up to a global phase.
many-runs : StdGen -> ℕ -> Float -> ℕ -> Bool -> IO {0ℓ} ⊤ᵖ
many-runs g n prec-d effort phase = do
  results <- sequenceIO (List.map run1 (expand-seed n g))
  many-runs-output n prec-d results
  where
    run2 : ℤ × StdGen -> IO RunResult
    run2 (theta' , g') = one-run g' (Div (Times (Const theta') Pi) (Const (+ 2048))) prec-d effort phase
    run1 : StdGen -> IO RunResult
    run1 g = run2 (randomR (+ 0 , + 2047) g)

-- Generate the table of "Experimental Results" used in the article.
main-maketable : Options -> IO {0ℓ} ⊤ᵖ
main-maketable options = do
  g <- get-seed (opt-rseed options)
  putStrLn ("% Initial random seed: " ++ show g)
  putStrLn ""
  sequenceIO′ (List.zipWith task precisions (expand-seed (List.length precisions) g))
  where
    theta : SymReal
    theta with opt-theta options
    ... | nothing = Div Pi (Const (+ 128))
    ... | just t = t
    count : ℕ
    count with opt-count options
    ... | nothing = 50
    ... | just c = c
    precisions : List Float
    precisions with opt-digits options
    ... | nothing = 10.0 ∷ 20.0 ∷ 30.0 ∷ 40.0 ∷ 50.0 ∷ 60.0 ∷ 70.0 ∷ 80.0 ∷ 90.0 ∷ 100.0 ∷ 200.0 ∷ 500.0 ∷ 1000.0 ∷ []
    ... | just d = d ∷ []
    effort = opt-effort options
    phase = opt-phase options
    task2 : Float -> StdGen × StdGen -> IO {0ℓ} ⊤ᵖ
    task2 prec-d (g1 , g2) = do
      _ <- one-run g1 theta prec-d effort phase
      many-runs g2 count prec-d effort phase
    task : Float -> StdGen -> IO {0ℓ} ⊤ᵖ
    task prec-d g = task2 prec-d (split g)

-- Main function: read options, then execute the appropriate tasks.
main : Main
main = run do
  argv <- getArgs
  options <- dopts argv
  if opt-table options then main-maketable options else main-default options
