-- A port of the Haskell module System.Console.GetOpt (from GHC's base
-- library), which the gridsynth command line program uses to process
-- its options. The behavior (option matching, permutation of
-- non-options, error messages, usage text) is that of base-4.20.
--
-- Differences from Haskell:
--
-- * Strings are Agda Strings (converted to lists of characters
--   internally); an option is given by the constructor Option' (the
--   name Option would clash with the type).
-- * The processing of the argument list is not structurally recursive
--   (a cluster "-abc" is split into "-a" and "-bc"); it is bounded by
--   a fuel argument that is always sufficient (the total number of
--   characters plus the number of arguments).

{-# OPTIONS --without-K --safe #-}

module Programs.GetOpt where

open import Level using (Level)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String.Base as String using (String)

private
  variable
    a : Level

-- ----------------------------------------------------------------------
-- * Option descriptions

-- What to do with options following non-options.
data ArgOrder {a : Level} (A : Set a) : Set a where
  -- no option processing after the first non-option
  RequireOrder : ArgOrder A
  -- freely intersperse options and non-options
  Permute : ArgOrder A
  -- wrap non-options into options
  ReturnInOrder : (String -> A) -> ArgOrder A

-- Describes whether an option takes an argument or not, and if so how
-- the argument is injected into a value of type A.
data ArgDescr {a : Level} (A : Set a) : Set a where
  -- no argument expected
  NoArg : A -> ArgDescr A
  -- option requires argument (with its description)
  ReqArg : (String -> A) -> String -> ArgDescr A
  -- optional argument
  OptArg : (Maybe String -> A) -> String -> ArgDescr A

-- Each OptDescr describes a single option: the list of short option
-- characters, the list of long option strings (without "--"), the
-- argument descriptor, and the explanation of the option for the
-- user.
record OptDescr {a : Level} (A : Set a) : Set a where
  constructor Option'
  field
    opt-short : List Char
    opt-long : List String
    opt-arg : ArgDescr A
    opt-descr : String
open OptDescr public

-- ----------------------------------------------------------------------
-- * Auxiliary list functions

private
  Str : Set
  Str = List Char

  str : Str -> String
  str = String.fromList

  chars : String -> Str
  chars = String.toList

  _==c_ : Char -> Char -> Bool
  a ==c b = Char.toℕ a Nat.≡ᵇ Char.toℕ b

  eqStr : Str -> Str -> Bool
  eqStr [] [] = true
  eqStr (a ∷ as) (b ∷ bs) = (a ==c b) ∧ eqStr as bs
  eqStr _ _ = false

  isPrefixOf : Str -> Str -> Bool
  isPrefixOf [] _ = true
  isPrefixOf (a ∷ as) [] = false
  isPrefixOf (a ∷ as) (b ∷ bs) = (a ==c b) ∧ isPrefixOf as bs

  any : {A : Set a} -> (A -> Bool) -> List A -> Bool
  any p [] = false
  any p (x ∷ xs) = p x ∨ any p xs

  -- break (== '=')
  breakEq : Str -> Str × Str
  breakEq [] = [] , []
  breakEq (c ∷ cs) with c ==c '='
  ... | true = [] , c ∷ cs
  ... | false with breakEq cs
  ...   | a , b = c ∷ a , b

  breakNL : Str -> Str × Str
  breakNL [] = [] , []
  breakNL (c ∷ cs) with c ==c '\n'
  ... | true = [] , c ∷ cs
  ... | false with breakNL cs
  ...   | a , b = c ∷ a , b

  -- Haskell's lines (the first argument is fuel).
  lines' : ℕ -> Str -> List Str
  lines' _ [] = []
  lines' zero s = s ∷ []
  lines' (suc f) s@(_ ∷ _) with breakNL s
  ... | l , [] = l ∷ []
  ... | l , (_ ∷ rest) = l ∷ lines' f rest

  lines : Str -> List Str
  lines s = lines' (List.length s) s

  maximum : List ℕ -> ℕ
  maximum = List.foldr Nat._⊔_ 0

  flushLeft : ℕ -> List Str -> List Str
  flushLeft n xs = List.map (λ x -> List.take n (x ++ List.replicate n ' ')) xs

  sameLen : List Str -> List Str
  sameLen xs = flushLeft (maximum (List.map List.length xs)) xs

  unzip3 : {A B C : Set} -> List (A × B × C) -> List A × List B × List C
  unzip3 [] = [] , [] , []
  unzip3 ((a , b , c) ∷ xs) with unzip3 xs
  ... | as , bs , cs = a ∷ as , b ∷ bs , c ∷ cs

  zipWith3 : {A B C D : Set} -> (A -> B -> C -> D) -> List A -> List B -> List C -> List D
  zipWith3 f (a ∷ as) (b ∷ bs) (c ∷ cs) = f a b c ∷ zipWith3 f as bs cs
  zipWith3 f _ _ _ = []

  unlines : List Str -> Str
  unlines = List.concatMap (λ l -> l ++ '\n' ∷ [])

-- ----------------------------------------------------------------------
-- * Usage information

private
  fmtShort : {A : Set a} -> ArgDescr A -> Char -> Str
  fmtShort (NoArg _) so = '-' ∷ so ∷ []
  fmtShort (ReqArg _ ad) so = '-' ∷ so ∷ ' ' ∷ chars ad
  fmtShort (OptArg _ ad) so = '-' ∷ so ∷ '[' ∷ chars ad ++ ']' ∷ []

  fmtLong : {A : Set a} -> ArgDescr A -> String -> Str
  fmtLong (NoArg _) lo = '-' ∷ '-' ∷ chars lo
  fmtLong (ReqArg _ ad) lo = '-' ∷ '-' ∷ chars lo ++ '=' ∷ chars ad
  fmtLong (OptArg _ ad) lo = '-' ∷ '-' ∷ chars lo ++ '[' ∷ '=' ∷ chars ad ++ ']' ∷ []

  sepBy : Char -> List Str -> Str
  sepBy _ [] = []
  sepBy _ (x ∷ []) = x
  sepBy ch (x ∷ xs@(_ ∷ _)) = x ++ ch ∷ ' ' ∷ sepBy ch xs

  fmtOpt : {A : Set a} -> OptDescr A -> List (Str × Str × Str)
  fmtOpt (Option' sos los ad descr) with lines (chars descr)
  ... | [] = (sosFmt , losFmt , []) ∷ []
    where
      sosFmt = sepBy ',' (List.map (fmtShort ad) sos)
      losFmt = sepBy ',' (List.map (fmtLong ad) los)
  ... | d ∷ ds = (sosFmt , losFmt , d) ∷ List.map (λ d' -> [] , [] , d') ds
    where
      sosFmt = sepBy ',' (List.map (fmtShort ad) sos)
      losFmt = sepBy ',' (List.map (fmtLong ad) los)

  paste : Str -> Str -> Str -> Str
  paste x y z = ' ' ∷ ' ' ∷ x ++ ' ' ∷ ' ' ∷ y ++ ' ' ∷ ' ' ∷ z

  usageTable : List (Str × Str × Str) -> List Str
  usageTable ts with unzip3 ts
  ... | ss , ls , ds = zipWith3 paste (sameLen ss) (sameLen ls) ds

-- Return a string describing the usage of a command, derived from the
-- header (first argument) and the options described by the second
-- argument.
usageInfo : {A : Set a} -> String -> List (OptDescr A) -> String
usageInfo header optDescr =
  str (unlines (chars header ∷ usageTable (List.concatMap fmtOpt optDescr)))

-- ----------------------------------------------------------------------
-- * Option processing

private
  data OptKind {a : Level} (A : Set a) : Set a where
    Opt : A -> OptKind A            -- an option
    UnreqOpt : String -> OptKind A  -- an unrecognized option
    NonOpt : String -> OptKind A    -- a non-option
    EndOfOpts : OptKind A           -- end-of-options marker (i.e. "--")
    OptErr : String -> OptKind A    -- something went wrong...

  errAmbig : {A : Set a} -> List (OptDescr A) -> Str -> OptKind A
  errAmbig ods optStr = OptErr (usageInfo ("option `" String.++ str optStr String.++ "' is ambiguous; could be one of:") ods)

  errReq : {A : Set a} -> String -> Str -> OptKind A
  errReq d optStr = OptErr ("option `" String.++ str optStr String.++ "' requires an argument " String.++ d String.++ "\n")

  errUnrec : String -> String
  errUnrec optStr = "unrecognized option `" String.++ optStr String.++ "'\n"

  errNoArg : {A : Set a} -> Str -> OptKind A
  errNoArg optStr = OptErr ("option `" String.++ str optStr String.++ "' doesn't allow an argument\n")

  -- Handle a long option "--ls".
  longOpt : {A : Set a} -> Str -> List Str -> List (OptDescr A) -> OptKind A × List Str
  longOpt {A = A} ls rs optDescr with breakEq ls
  ... | opt , arg = long (List.map opt-arg options) arg rs
    where
      getWith : (Str -> Str -> Bool) -> List (OptDescr A)
      getWith p = List.filterᵇ (λ o -> any (λ x -> p opt (chars x)) (opt-long o)) optDescr

      exact = getWith eqStr
      options : List (OptDescr A)
      options with exact
      ... | [] = getWith isPrefixOf
      ... | ex@(_ ∷ _) = ex

      optStr : Str
      optStr = '-' ∷ '-' ∷ opt

      long : List (ArgDescr A) -> Str -> List Str -> OptKind A × List Str
      long (_ ∷ _ ∷ _) _ rest = errAmbig options optStr , rest
      long (NoArg a ∷ []) [] rest = Opt a , rest
      long (NoArg _ ∷ []) ('=' ∷ _) rest = errNoArg optStr , rest
      long (ReqArg _ d ∷ []) [] [] = errReq d optStr , []
      long (ReqArg f _ ∷ []) [] (r ∷ rest) = Opt (f (str r)) , rest
      long (ReqArg f _ ∷ []) ('=' ∷ xs) rest = Opt (f (str xs)) , rest
      long (OptArg f _ ∷ []) [] rest = Opt (f nothing) , rest
      long (OptArg f _ ∷ []) ('=' ∷ xs) rest = Opt (f (just (str xs))) , rest
      long _ _ rest = UnreqOpt (str ('-' ∷ '-' ∷ ls)) , rest

  -- Handle a short option "-y" followed by the characters ys.
  shortOpt : {A : Set a} -> Char -> Str -> List Str -> List (OptDescr A) -> OptKind A × List Str
  shortOpt {A = A} y ys rs optDescr = short (List.map opt-arg options) ys rs
    where
      options : List (OptDescr A)
      options = List.filterᵇ (λ o -> any (λ s -> y ==c s) (opt-short o)) optDescr

      optStr : Str
      optStr = '-' ∷ y ∷ []

      short : List (ArgDescr A) -> Str -> List Str -> OptKind A × List Str
      short (_ ∷ _ ∷ _) _ rest = errAmbig options optStr , rest
      short (NoArg a ∷ _) [] rest = Opt a , rest
      short (NoArg a ∷ _) xs@(_ ∷ _) rest = Opt a , ('-' ∷ xs) ∷ rest
      short (ReqArg _ d ∷ _) [] [] = errReq d optStr , []
      short (ReqArg f _ ∷ _) [] (r ∷ rest) = Opt (f (str r)) , rest
      short (ReqArg f _ ∷ _) xs@(_ ∷ _) rest = Opt (f (str xs)) , rest
      short (OptArg f _ ∷ _) [] rest = Opt (f nothing) , rest
      short (OptArg f _ ∷ _) xs@(_ ∷ _) rest = Opt (f (just (str xs))) , rest
      short [] [] rest = UnreqOpt (str optStr) , rest
      short [] xs@(_ ∷ _) rest = UnreqOpt (str optStr) , ('-' ∷ xs) ∷ rest

  -- Take a look at the next command line argument and decide what to
  -- do with it.
  getNext : {A : Set a} -> Str -> List Str -> List (OptDescr A) -> OptKind A × List Str
  getNext ('-' ∷ '-' ∷ []) rest _ = EndOfOpts , rest
  getNext ('-' ∷ '-' ∷ xs@(_ ∷ _)) rest optDescr = longOpt xs rest optDescr
  getNext ('-' ∷ x ∷ xs) rest optDescr = shortOpt x xs rest optDescr
  getNext a rest _ = NonOpt (str a) , rest

  Result : Set a -> Set a
  Result A = List A × List String × List String × List String

  -- getOpt' with fuel.
  getOpt'' : {A : Set a} -> ℕ -> ArgOrder A -> List (OptDescr A) -> List Str -> Result A
  getOpt'' _ ordering optDescr [] = [] , [] , [] , []
  getOpt'' zero ordering optDescr args@(_ ∷ _) = [] , List.map str args , [] , []
  getOpt'' {A = A} (suc f) ordering optDescr (arg ∷ args) with getNext arg args optDescr
  ... | opt , rest = procNextOpt opt ordering
    where
      recur : Result A
      recur = getOpt'' f ordering optDescr rest

      procNextOpt : OptKind A -> ArgOrder A -> Result A
      procNextOpt (Opt o) _ with recur
      ... | os , xs , us , es = o ∷ os , xs , us , es
      procNextOpt (UnreqOpt u) _ with recur
      ... | os , xs , us , es = os , xs , u ∷ us , es
      procNextOpt (NonOpt a) RequireOrder = [] , a ∷ List.map str rest , [] , []
      procNextOpt (NonOpt a) Permute with recur
      ... | os , xs , us , es = os , a ∷ xs , us , es
      procNextOpt (NonOpt a) (ReturnInOrder g) with recur
      ... | os , xs , us , es = g a ∷ os , xs , us , es
      procNextOpt EndOfOpts RequireOrder = [] , List.map str rest , [] , []
      procNextOpt EndOfOpts Permute = [] , List.map str rest , [] , []
      procNextOpt EndOfOpts (ReturnInOrder g) = List.map (λ r -> g (str r)) rest , [] , [] , []
      procNextOpt (OptErr e) _ with recur
      ... | os , xs , us , es = os , xs , us , e ∷ es

  fuel-of : List Str -> ℕ
  fuel-of args = List.foldr Nat._+_ 0 (List.map (λ a -> suc (List.length a)) args)

-- This is almost the same as getOpt, but returns a quadruple
-- consisting of the option arguments, a list of non-options, a list
-- of unrecognized options, and a list of error messages.
getOpt' : {A : Set a} -> ArgOrder A -> List (OptDescr A) -> List String -> List A × List String × List String × List String
getOpt' ordering optDescr args = getOpt'' (fuel-of cargs) ordering optDescr cargs
  where
    cargs = List.map chars args

-- Process the command-line, and return the list of values that
-- matched (and those that didn't). The arguments are:
--
-- * The order requirements (see ArgOrder)
-- * The option descriptions (see OptDescr)
-- * The actual command line arguments (presumably got from getArgs).
--
-- getOpt returns a triple consisting of the option arguments, a list
-- of non-options, and a list of error messages.
getOpt : {A : Set a} -> ArgOrder A -> List (OptDescr A) -> List String -> List A × List String × List String
getOpt ordering optDescr args with getOpt' ordering optDescr args
... | os , xs , us , es = os , xs , es ++ List.map errUnrec us
