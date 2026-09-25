-- The generalized permutations of Kopt.Descent as symbolic data, and
-- the exhaustive check over all 6144 of them.
--
-- This module holds the machinery that both Kopt.Optimality and
-- Kopt.SynthProperties need to know that gperm-of returns, for every
-- generalized permutation G, a circuit implementing G exactly with at
-- most 9 gates, no K gate and at most one CS gate (Section III C):
--
--   * gate-gp?, gp-of-gate, gate-gp-ok: the gates of 𝒢 other than
--     K₀, K₁ (and the derived CK, KC) are generalized permutations;
--
--   * pos#, ph#, gperm-of-gp-mat: gperm-of reads the permutation and
--     the phases off gp-mat-of t e, so its circuit is
--     gperm-circuit-for -- proved once, generically;
--
--   * GPData, sem-gpd, sem-gpd-sound: the generalized permutation a
--     K-free circuit implements, as a COMPUTATION on the
--     permutation/phase data rather than on 4×4 matrices over 𝔻[i],
--     proved sound once and symbolically;
--
--   * gp-check-perm-ok: the exhaustive check over the 24·256 = 6144
--     generalized permutations, in 24 blocks of 256.
--
-- Doing the check on the symbolic data rather than on the matrices is
-- what makes it cheap: the conversion checker is never asked to
-- decide that two different expressions denote the same concrete 4×4
-- matrix over 𝔻[i] (Matrix, _[i]_ and Dyadic are records with eta, so
-- such a decision drags in the whole dyadic arithmetic). Nothing is
-- weakened: the check is still over all 6144 generalized
-- permutations, and still verifies all five properties.

{-# OPTIONS --without-K --safe #-}

module Kopt.GPData where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_×_ ; _,_ ; Σ ; Σ-syntax ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; subst₂)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Matrix
open import Kopt.Base
open import Kopt.Gates
open import Kopt.Permutations using (Tuple4 ; distinct4 ; column-info ; gperm-data ;
                                     gperm-data-of ; gperm-of-data ; gperm-of ;
                                     gperm-circuit-for)
open import Kopt.Descent

-- ----------------------------------------------------------------------
-- * Booleans as propositions

private
  false≢true : false ≡ true -> ⊥
  false≢true ()

-- A boolean equality test that succeeds is an equality.
==⇒≡ : {A : Set} {{_ : DecEq A}} {x y : A} -> (x == y) ≡ true -> x ≡ y
==⇒≡ {x = x} {y} e with x ≟ y
... | yes p = p
... | no _ = ⊥-elim (false≢true e)

≤ᵇ⇒≤ : {m n : ℕ} -> (m Nat.≤ᵇ n) ≡ true -> m Nat.≤ n
≤ᵇ⇒≤ {m} {n} e = NatP.≤ᵇ⇒≤ m n (subst T (sym e) tt)

≡ᵇ⇒≡ : {m n : ℕ} -> (m Nat.≡ᵇ n) ≡ true -> m ≡ n
≡ᵇ⇒≡ {m} {n} e = NatP.≡ᵇ⇒≡ m n (subst T (sym e) tt)


-- ----------------------------------------------------------------------
-- * The gates that are generalized permutations

-- Which gates are generalized permutations: all of 𝒢 except K₀ and
-- K₁ (and the derived gates CK and KC, which contain a K).
gate-gp? : Gate -> Bool
gate-gp? K₀ = false
gate-gp? K₁ = false
gate-gp? CK = false
gate-gp? KC = false
gate-gp? _ = true

gp-of-gate : Gate -> GP
gp-of-gate X₀ = gperm (p2 , p3 , p0 , p1) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate X₁ = gperm (p1 , p0 , p3 , p2) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate Z₀ = gperm id4p (ph0 , ph0 , ph2 , ph2) refl
gp-of-gate Z₁ = gperm id4p (ph0 , ph2 , ph0 , ph2) refl
gp-of-gate S₀ = gperm id4p (ph0 , ph0 , ph1 , ph1) refl
gp-of-gate S₁ = gperm id4p (ph0 , ph1 , ph0 , ph1) refl
gp-of-gate CZ = gperm id4p (ph0 , ph0 , ph0 , ph2) refl
gp-of-gate CS = gperm id4p (ph0 , ph0 , ph0 , ph1) refl
gp-of-gate CX = gperm (p0 , p1 , p3 , p2) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate XC = gperm (p0 , p3 , p2 , p1) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate Ex = gperm (p0 , p2 , p1 , p3) (ph0 , ph0 , ph0 , ph0) refl
gp-of-gate Ii = gperm id4p (ph1 , ph1 , ph1 , ph1) refl
gp-of-gate _ = gp-one

-- Every gate of 𝒢 except K₀ and K₁ is a generalized permutation.
gate-gp-ok : (g : Gate) -> gate-gp? g ≡ true -> ⟦ g ⟧g ≡ gp-mat (gp-of-gate g)
gate-gp-ok K₀ ()
gate-gp-ok K₁ ()
gate-gp-ok CK ()
gate-gp-ok KC ()
gate-gp-ok X₀ _ = ==⇒≡ refl
gate-gp-ok X₁ _ = ==⇒≡ refl
gate-gp-ok Z₀ _ = ==⇒≡ refl
gate-gp-ok Z₁ _ = ==⇒≡ refl
gate-gp-ok S₀ _ = ==⇒≡ refl
gate-gp-ok S₁ _ = ==⇒≡ refl
gate-gp-ok CZ _ = ==⇒≡ refl
gate-gp-ok CS _ = ==⇒≡ refl
gate-gp-ok CX _ = ==⇒≡ refl
gate-gp-ok XC _ = ==⇒≡ refl
gate-gp-ok Ex _ = ==⇒≡ refl
gate-gp-ok Ii _ = ==⇒≡ refl

-- ----------------------------------------------------------------------
-- * The five properties of a canonical generalized-permutation circuit

-- The circuit implements the operator exactly, with at most 9 gates,
-- no K gate, at most one CS gate, over the gate set 𝒢.
GPProps : Op -> Circuit -> Set
GPProps m c = (⟦ c ⟧ ≡ m) × (rlen c Nat.≤ 9) × (kc c ≡ 0) × (csc c Nat.≤ 1) × Over𝒢 c

-- ** What gperm-of returns for a generalized permutation
--
-- gperm-of reads the permutation and the phases off the matrix. For a
-- matrix that is gp-mat-of t e this gives back t and e, as tuples of
-- natural numbers, so the circuit is gperm-circuit-for. Proving this
-- once, generically, removes 6144 evaluations of gperm-of (and of the
-- 4×4 matrix equality tests it does) from the check below.

-- The four coordinates and the four powers of i, as numbers.
pos# : Pos -> ℕ
pos# p0 = 0
pos# p1 = 1
pos# p2 = 2
pos# p3 = 3

ph# : Phase -> ℕ
ph# ph0 = 0
ph# ph1 = 1
ph# ph2 = 2
ph# ph3 = 3

pos#4 : Pos4 -> Tuple4
pos#4 (a , b , c , d) = pos# a , pos# b , pos# c , pos# d

ph#4 : Phase4 -> Tuple4
ph#4 (a , b , c , d) = ph# a , ph# b , ph# c , ph# d

private
  cong₄ : {A B C D E : Set} (f : A -> B -> C -> D -> E)
          {a a' : A} {b b' : B} {c c' : C} {d d' : D} ->
          a ≡ a' -> b ≡ b' -> c ≡ c' -> d ≡ d' -> f a b c d ≡ f a' b' c' d'
  cong₄ f refl refl refl refl = refl

  just-inj : {A : Set} {x y : A} -> just x ≡ just y -> x ≡ y
  just-inj refl = refl

  -- The column i^k·e_r is recognised as such: sixteen small
  -- computations instead of 6144 large ones.
  column-info-unit : (r : Pos) (c : Phase) -> column-info (unit-vec r c) ≡ just (pos# r , ph# c)
  column-info-unit p0 ph0 = refl
  column-info-unit p0 ph1 = refl
  column-info-unit p0 ph2 = refl
  column-info-unit p0 ph3 = refl
  column-info-unit p1 ph0 = refl
  column-info-unit p1 ph1 = refl
  column-info-unit p1 ph2 = refl
  column-info-unit p1 ph3 = refl
  column-info-unit p2 ph0 = refl
  column-info-unit p2 ph1 = refl
  column-info-unit p2 ph2 = refl
  column-info-unit p2 ph3 = refl
  column-info-unit p3 ph0 = refl
  column-info-unit p3 ph1 = refl
  column-info-unit p3 ph2 = refl
  column-info-unit p3 ph3 = refl

  -- pos# is injective, so the two distinctness tests agree.
  /=-pos# : (x y : Pos) -> (pos# x /= pos# y) ≡ not (x ==p y)
  /=-pos# p0 p0 = refl
  /=-pos# p0 p1 = refl
  /=-pos# p0 p2 = refl
  /=-pos# p0 p3 = refl
  /=-pos# p1 p0 = refl
  /=-pos# p1 p1 = refl
  /=-pos# p1 p2 = refl
  /=-pos# p1 p3 = refl
  /=-pos# p2 p0 = refl
  /=-pos# p2 p1 = refl
  /=-pos# p2 p2 = refl
  /=-pos# p2 p3 = refl
  /=-pos# p3 p0 = refl
  /=-pos# p3 p1 = refl
  /=-pos# p3 p2 = refl
  /=-pos# p3 p3 = refl

  distinct4-pos# : (t : Pos4) -> distinct4 (pos#4 t) ≡ distinct4p t
  distinct4-pos# (a , b , c , d) =
    cong₂ _∧_ (/=-pos# a b)
      (cong₂ _∧_ (/=-pos# a c)
        (cong₂ _∧_ (/=-pos# a d)
          (cong₂ _∧_ (/=-pos# b c)
            (cong₂ _∧_ (/=-pos# b d) (/=-pos# c d)))))

-- gperm-of returns a circuit for every generalized permutation,
-- namely the one that gperm-circuit-for computes from its
-- permutation and phase data.
gperm-of-gp-mat : (t : Pos4) (e : Phase4) -> distinct4p t ≡ true ->
                  gperm-of (gp-mat-of t e) ≡ just (gperm-circuit-for (pos#4 t) (ph#4 e))
gperm-of-gp-mat (a , b , c , d) (w , x , y , z) h = cong gperm-of-data step
  where
    tup : Tuple4 × Tuple4
    tup = (pos# a , pos# b , pos# c , pos# d) , (ph# w , ph# x , ph# y , ph# z)

    dh : distinct4 (pos# a , pos# b , pos# c , pos# d) ≡ true
    dh = trans (distinct4-pos# (a , b , c , d)) h

    step : gperm-data (gp-mat-of (a , b , c , d) (w , x , y , z)) ≡ just tup
    step = trans (cong₄ gperm-data-of (column-info-unit a w) (column-info-unit b x)
                                      (column-info-unit c y) (column-info-unit d z))
                 (cong (λ β -> if β then just tup else nothing) dh)

-- ----------------------------------------------------------------------
-- ** The exhaustive check over the 6144 generalized permutations
--
-- The circuit is checked against the generalized permutation on the
-- permutation/phase data of Kopt.Descent rather than on 4×4 matrices
-- over 𝔻[i]: sem-gpd is the kfree-gp of Kopt.Optimality as a
-- computation, and comparing its result with (t,e) costs a handful of
-- lookups in a four-element type instead of eight 4×4 matrix products.
-- (With the matrix products this check exhausted a 3 GB heap.) The
-- computation is on bare Pos4 × Phase4 data rather than on the record
-- GP, because gp-comp carries a distinctness proof whose term grows
-- with the length of the circuit; the distinctness is needed only in
-- the soundness proof below, which is done once and symbolically.

private
  GPData : Set
  GPData = Pos4 × Phase4

  -- The data of gp-comp, without its proof (gpd-comp-ok below says
  -- that this really is the data of gp-comp).
  gpd-comp : GPData -> GPData -> GPData
  gpd-comp (t , e) (s , f) = comp4p t s , (ph p0 , ph p1 , ph p2 , ph p3)
    where
      ph : Pos -> Phase
      ph j = selph f j ·p selph e (selp s j)

  gpd-of-gate : Gate -> GPData
  gpd-of-gate g = gp-pos (gp-of-gate g) , gp-ph (gp-of-gate g)

  gpd-one : GPData
  gpd-one = id4p , (ph0 , ph0 , ph0 , ph0)

  -- The generalized permutation implemented by a K-free circuit;
  -- nothing if the circuit contains a K gate.
  sem-gpd-cons : Bool -> GPData -> Maybe GPData -> Maybe GPData
  sem-gpd-cons true H (just G) = just (gpd-comp H G)
  sem-gpd-cons _ _ _ = nothing

  sem-gpd : Circuit -> Maybe GPData
  sem-gpd [] = just gpd-one
  sem-gpd (g ∷ c) = sem-gpd-cons (gate-gp? g) (gpd-of-gate g) (sem-gpd c)

  ,-inj : {A B : Set} {a a' : A} {b b' : B} -> (A × B ∋ (a , b)) ≡ (a' , b') ->
          (a ≡ a') × (b ≡ b')
  ,-inj refl = refl , refl

  -- gpd-comp computes the data of gp-comp: both sides are the same
  -- pair of tuples by definition.
  gpd-comp-ok : (H G : GP) ->
                gp-mat-of (proj₁ (gpd-comp (gp-pos H , gp-ph H) (gp-pos G , gp-ph G)))
                          (proj₂ (gpd-comp (gp-pos H , gp-ph H) (gp-pos G , gp-ph G)))
                ≡ gp-mat (gp-comp H G)
  gpd-comp-ok H G = refl

  sem-gpd-cons-sound :
    (g : Gate) (c : Circuit) (b : Bool) -> gate-gp? g ≡ b -> (x : Maybe GPData) ->
    ((s : Pos4) (f : Phase4) -> x ≡ just (s , f) ->
       (distinct4p s ≡ true) × (⟦ c ⟧ ≡ gp-mat-of s f)) ->
    (t : Pos4) (e : Phase4) -> sem-gpd-cons b (gpd-of-gate g) x ≡ just (t , e) ->
    (distinct4p t ≡ true) × (⟦ g ∷ c ⟧ ≡ gp-mat-of t e)
  sem-gpd-cons-sound g c true hg (just (s , f)) ih t e eq =
    subst (λ z -> distinct4p z ≡ true) (proj₁ dat) dist ,
    subst₂ (λ z w -> ⟦ g ∷ c ⟧ ≡ gp-mat-of z w) (proj₁ dat) (proj₂ dat) sem
    where
      rec : (distinct4p s ≡ true) × (⟦ c ⟧ ≡ gp-mat-of s f)
      rec = ih s f refl

      G : GP
      G = gperm s f (proj₁ rec)

      H : GP
      H = gp-of-gate g

      dat : (proj₁ (gpd-comp (gpd-of-gate g) (s , f)) ≡ t) ×
            (proj₂ (gpd-comp (gpd-of-gate g) (s , f)) ≡ e)
      dat = ,-inj (just-inj eq)

      dist : distinct4p (proj₁ (gpd-comp (gpd-of-gate g) (s , f))) ≡ true
      dist = gp-distinct (gp-comp H G)

      sem : ⟦ g ∷ c ⟧ ≡ gp-mat-of (proj₁ (gpd-comp (gpd-of-gate g) (s , f)))
                                  (proj₂ (gpd-comp (gpd-of-gate g) (s , f)))
      sem = trans (trans (cong₂ _*_ (gate-gp-ok g hg) (proj₂ rec))
                         (gp-mat-comp H G))
                  (sym (gpd-comp-ok H G))
  sem-gpd-cons-sound g c true hg nothing ih t e ()
  sem-gpd-cons-sound g c false hg x ih t e ()

  sem-gpd-sound : (c : Circuit) (t : Pos4) (e : Phase4) -> sem-gpd c ≡ just (t , e) ->
                  (distinct4p t ≡ true) × (⟦ c ⟧ ≡ gp-mat-of t e)
  sem-gpd-sound [] t e eq =
    subst (λ z -> distinct4p z ≡ true) (proj₁ dat) refl ,
    subst₂ (λ z w -> ⟦ [] ⟧ ≡ gp-mat-of z w) (proj₁ dat) (proj₂ dat) (sym gp-one-mat)
    where
      dat : ((Pos4 ∋ id4p) ≡ t) × ((Phase4 ∋ (ph0 , ph0 , ph0 , ph0)) ≡ e)
      dat = ,-inj (just-inj eq)
  sem-gpd-sound (g ∷ c) t e eq =
    sem-gpd-cons-sound g c (gate-gp? g) refl (sem-gpd c) (sem-gpd-sound c) t e eq

  -- Boolean equality of phases and of phase vectors (Kopt.Descent has
  -- the ones for the coordinates).
  infix 4 _==ph_
  _==ph_ : Phase -> Phase -> Bool
  ph0 ==ph ph0 = true
  ph1 ==ph ph1 = true
  ph2 ==ph ph2 = true
  ph3 ==ph ph3 = true
  _ ==ph _ = false

  ==ph-sound : {x y : Phase} -> (x ==ph y) ≡ true -> x ≡ y
  ==ph-sound {ph0} {ph0} _ = refl
  ==ph-sound {ph1} {ph1} _ = refl
  ==ph-sound {ph2} {ph2} _ = refl
  ==ph-sound {ph3} {ph3} _ = refl

  eq4ph : Phase4 -> Phase4 -> Bool
  eq4ph (a , b , c , d) (a' , b' , c' , d') =
    (a ==ph a') ∧ (b ==ph b') ∧ (c ==ph c') ∧ (d ==ph d')

  -- As for eq4p-sound in Kopt.Descent: the four boolean tests are
  -- brought into scope with "with ... in", because the unifier does not
  -- decompose a conjunction, so the implicit arguments of ∧-true
  -- cannot be inferred from a nested ∧.
  eq4ph-sound : {u v : Phase4} -> eq4ph u v ≡ true -> u ≡ v
  eq4ph-sound {a , b , c , d} {a' , b' , c' , d'} h
    with a ==ph a' in ea | b ==ph b' in eb | c ==ph c' in ec | d ==ph d' in ed
  ... | true | true | true | true =
        cong₂ _,_ (==ph-sound ea)
          (cong₂ _,_ (==ph-sound eb) (cong₂ _,_ (==ph-sound ec) (==ph-sound ed)))

  gpd-eq? : GPData -> Pos4 -> Phase4 -> Bool
  gpd-eq? (s , f) t e = eq4p s t ∧ eq4ph f e

  gpd-sem-eq? : Maybe GPData -> Pos4 -> Phase4 -> Bool
  gpd-sem-eq? nothing t e = false
  gpd-sem-eq? (just G) t e = gpd-eq? G t e

  gpd-sem-sound : (t : Pos4) (e : Phase4) (c : Circuit) (x : Maybe GPData) ->
                  ((s : Pos4) (f : Phase4) -> x ≡ just (s , f) ->
                     (distinct4p s ≡ true) × (⟦ c ⟧ ≡ gp-mat-of s f)) ->
                  gpd-sem-eq? x t e ≡ true -> ⟦ c ⟧ ≡ gp-mat-of t e
  gpd-sem-sound t e c (just (s , f)) ih h =
    trans (proj₂ (ih s f refl))
          (cong₂ gp-mat-of (eq4p-sound (proj₁ parts)) (eq4ph-sound (proj₂ parts)))
    where
      parts : (eq4p s t ≡ true) × (eq4ph f e ≡ true)
      parts = ∧-true {eq4p s t} {eq4ph f e} h
  gpd-sem-sound t e c nothing ih ()

  -- The five properties of a canonical generalized-permutation
  -- circuit, as one boolean test.
  gp-ok? : Pos4 -> Phase4 -> Circuit -> Bool
  gp-ok? t e c = gpd-sem-eq? (sem-gpd c) t e ∧ (rlen c Nat.≤ᵇ 9) ∧ (kc c Nat.≡ᵇ 0) ∧
                 (csc c Nat.≤ᵇ 1) ∧ over-𝒢ᵇ c

  gp-ok-props : (t : Pos4) (e : Phase4) (c : Circuit) -> gp-ok? t e c ≡ true ->
                GPProps (gp-mat-of t e) c
  gp-ok-props t e c h with ∧-true₅ h
  ... | (p₁ , p₂ , p₃ , p₄ , p₅) =
        gpd-sem-sound t e c (sem-gpd c) (sem-gpd-sound c) p₁ ,
        ≤ᵇ⇒≤ p₂ , ≡ᵇ⇒≡ p₃ , ≤ᵇ⇒≤ p₄ , p₅

  gp-check-phases : Pos4 -> Phase4 -> Bool
  gp-check-phases t e = gp-ok? t e (gperm-circuit-for (pos#4 t) (ph#4 e))

  -- The 256 phase vectors for one permutation, and then the 24
  -- permutations: 24 blocks of 256 rather than one enumeration of
  -- 6144 pairs, which keeps the type checker's heap smaller.
  gp-check-perm : Pos4 -> Bool
  gp-check-perm t = all-of (gp-check-phases t) all-phase4

  -- One conversion problem per permutation (24 blocks of 256 instead
  -- of one of 6144), so that the type checker can reclaim each block
  -- before starting the next one. The 232 tuples that are not
  -- permutations are ruled out by absurd patterns.
  gp-check-perm-ok : (a b c d : Pos) -> distinct4p (a , b , c , d) ≡ true ->
                     gp-check-perm (a , b , c , d) ≡ true
  gp-check-perm-ok p0 p0 p0 p0 ()
  gp-check-perm-ok p0 p0 p0 p1 ()
  gp-check-perm-ok p0 p0 p0 p2 ()
  gp-check-perm-ok p0 p0 p0 p3 ()
  gp-check-perm-ok p0 p0 p1 p0 ()
  gp-check-perm-ok p0 p0 p1 p1 ()
  gp-check-perm-ok p0 p0 p1 p2 ()
  gp-check-perm-ok p0 p0 p1 p3 ()
  gp-check-perm-ok p0 p0 p2 p0 ()
  gp-check-perm-ok p0 p0 p2 p1 ()
  gp-check-perm-ok p0 p0 p2 p2 ()
  gp-check-perm-ok p0 p0 p2 p3 ()
  gp-check-perm-ok p0 p0 p3 p0 ()
  gp-check-perm-ok p0 p0 p3 p1 ()
  gp-check-perm-ok p0 p0 p3 p2 ()
  gp-check-perm-ok p0 p0 p3 p3 ()
  gp-check-perm-ok p0 p1 p0 p0 ()
  gp-check-perm-ok p0 p1 p0 p1 ()
  gp-check-perm-ok p0 p1 p0 p2 ()
  gp-check-perm-ok p0 p1 p0 p3 ()
  gp-check-perm-ok p0 p1 p1 p0 ()
  gp-check-perm-ok p0 p1 p1 p1 ()
  gp-check-perm-ok p0 p1 p1 p2 ()
  gp-check-perm-ok p0 p1 p1 p3 ()
  gp-check-perm-ok p0 p1 p2 p0 ()
  gp-check-perm-ok p0 p1 p2 p1 ()
  gp-check-perm-ok p0 p1 p2 p2 ()
  gp-check-perm-ok p0 p1 p2 p3 _ = refl
  gp-check-perm-ok p0 p1 p3 p0 ()
  gp-check-perm-ok p0 p1 p3 p1 ()
  gp-check-perm-ok p0 p1 p3 p2 _ = refl
  gp-check-perm-ok p0 p1 p3 p3 ()
  gp-check-perm-ok p0 p2 p0 p0 ()
  gp-check-perm-ok p0 p2 p0 p1 ()
  gp-check-perm-ok p0 p2 p0 p2 ()
  gp-check-perm-ok p0 p2 p0 p3 ()
  gp-check-perm-ok p0 p2 p1 p0 ()
  gp-check-perm-ok p0 p2 p1 p1 ()
  gp-check-perm-ok p0 p2 p1 p2 ()
  gp-check-perm-ok p0 p2 p1 p3 _ = refl
  gp-check-perm-ok p0 p2 p2 p0 ()
  gp-check-perm-ok p0 p2 p2 p1 ()
  gp-check-perm-ok p0 p2 p2 p2 ()
  gp-check-perm-ok p0 p2 p2 p3 ()
  gp-check-perm-ok p0 p2 p3 p0 ()
  gp-check-perm-ok p0 p2 p3 p1 _ = refl
  gp-check-perm-ok p0 p2 p3 p2 ()
  gp-check-perm-ok p0 p2 p3 p3 ()
  gp-check-perm-ok p0 p3 p0 p0 ()
  gp-check-perm-ok p0 p3 p0 p1 ()
  gp-check-perm-ok p0 p3 p0 p2 ()
  gp-check-perm-ok p0 p3 p0 p3 ()
  gp-check-perm-ok p0 p3 p1 p0 ()
  gp-check-perm-ok p0 p3 p1 p1 ()
  gp-check-perm-ok p0 p3 p1 p2 _ = refl
  gp-check-perm-ok p0 p3 p1 p3 ()
  gp-check-perm-ok p0 p3 p2 p0 ()
  gp-check-perm-ok p0 p3 p2 p1 _ = refl
  gp-check-perm-ok p0 p3 p2 p2 ()
  gp-check-perm-ok p0 p3 p2 p3 ()
  gp-check-perm-ok p0 p3 p3 p0 ()
  gp-check-perm-ok p0 p3 p3 p1 ()
  gp-check-perm-ok p0 p3 p3 p2 ()
  gp-check-perm-ok p0 p3 p3 p3 ()
  gp-check-perm-ok p1 p0 p0 p0 ()
  gp-check-perm-ok p1 p0 p0 p1 ()
  gp-check-perm-ok p1 p0 p0 p2 ()
  gp-check-perm-ok p1 p0 p0 p3 ()
  gp-check-perm-ok p1 p0 p1 p0 ()
  gp-check-perm-ok p1 p0 p1 p1 ()
  gp-check-perm-ok p1 p0 p1 p2 ()
  gp-check-perm-ok p1 p0 p1 p3 ()
  gp-check-perm-ok p1 p0 p2 p0 ()
  gp-check-perm-ok p1 p0 p2 p1 ()
  gp-check-perm-ok p1 p0 p2 p2 ()
  gp-check-perm-ok p1 p0 p2 p3 _ = refl
  gp-check-perm-ok p1 p0 p3 p0 ()
  gp-check-perm-ok p1 p0 p3 p1 ()
  gp-check-perm-ok p1 p0 p3 p2 _ = refl
  gp-check-perm-ok p1 p0 p3 p3 ()
  gp-check-perm-ok p1 p1 p0 p0 ()
  gp-check-perm-ok p1 p1 p0 p1 ()
  gp-check-perm-ok p1 p1 p0 p2 ()
  gp-check-perm-ok p1 p1 p0 p3 ()
  gp-check-perm-ok p1 p1 p1 p0 ()
  gp-check-perm-ok p1 p1 p1 p1 ()
  gp-check-perm-ok p1 p1 p1 p2 ()
  gp-check-perm-ok p1 p1 p1 p3 ()
  gp-check-perm-ok p1 p1 p2 p0 ()
  gp-check-perm-ok p1 p1 p2 p1 ()
  gp-check-perm-ok p1 p1 p2 p2 ()
  gp-check-perm-ok p1 p1 p2 p3 ()
  gp-check-perm-ok p1 p1 p3 p0 ()
  gp-check-perm-ok p1 p1 p3 p1 ()
  gp-check-perm-ok p1 p1 p3 p2 ()
  gp-check-perm-ok p1 p1 p3 p3 ()
  gp-check-perm-ok p1 p2 p0 p0 ()
  gp-check-perm-ok p1 p2 p0 p1 ()
  gp-check-perm-ok p1 p2 p0 p2 ()
  gp-check-perm-ok p1 p2 p0 p3 _ = refl
  gp-check-perm-ok p1 p2 p1 p0 ()
  gp-check-perm-ok p1 p2 p1 p1 ()
  gp-check-perm-ok p1 p2 p1 p2 ()
  gp-check-perm-ok p1 p2 p1 p3 ()
  gp-check-perm-ok p1 p2 p2 p0 ()
  gp-check-perm-ok p1 p2 p2 p1 ()
  gp-check-perm-ok p1 p2 p2 p2 ()
  gp-check-perm-ok p1 p2 p2 p3 ()
  gp-check-perm-ok p1 p2 p3 p0 _ = refl
  gp-check-perm-ok p1 p2 p3 p1 ()
  gp-check-perm-ok p1 p2 p3 p2 ()
  gp-check-perm-ok p1 p2 p3 p3 ()
  gp-check-perm-ok p1 p3 p0 p0 ()
  gp-check-perm-ok p1 p3 p0 p1 ()
  gp-check-perm-ok p1 p3 p0 p2 _ = refl
  gp-check-perm-ok p1 p3 p0 p3 ()
  gp-check-perm-ok p1 p3 p1 p0 ()
  gp-check-perm-ok p1 p3 p1 p1 ()
  gp-check-perm-ok p1 p3 p1 p2 ()
  gp-check-perm-ok p1 p3 p1 p3 ()
  gp-check-perm-ok p1 p3 p2 p0 _ = refl
  gp-check-perm-ok p1 p3 p2 p1 ()
  gp-check-perm-ok p1 p3 p2 p2 ()
  gp-check-perm-ok p1 p3 p2 p3 ()
  gp-check-perm-ok p1 p3 p3 p0 ()
  gp-check-perm-ok p1 p3 p3 p1 ()
  gp-check-perm-ok p1 p3 p3 p2 ()
  gp-check-perm-ok p1 p3 p3 p3 ()
  gp-check-perm-ok p2 p0 p0 p0 ()
  gp-check-perm-ok p2 p0 p0 p1 ()
  gp-check-perm-ok p2 p0 p0 p2 ()
  gp-check-perm-ok p2 p0 p0 p3 ()
  gp-check-perm-ok p2 p0 p1 p0 ()
  gp-check-perm-ok p2 p0 p1 p1 ()
  gp-check-perm-ok p2 p0 p1 p2 ()
  gp-check-perm-ok p2 p0 p1 p3 _ = refl
  gp-check-perm-ok p2 p0 p2 p0 ()
  gp-check-perm-ok p2 p0 p2 p1 ()
  gp-check-perm-ok p2 p0 p2 p2 ()
  gp-check-perm-ok p2 p0 p2 p3 ()
  gp-check-perm-ok p2 p0 p3 p0 ()
  gp-check-perm-ok p2 p0 p3 p1 _ = refl
  gp-check-perm-ok p2 p0 p3 p2 ()
  gp-check-perm-ok p2 p0 p3 p3 ()
  gp-check-perm-ok p2 p1 p0 p0 ()
  gp-check-perm-ok p2 p1 p0 p1 ()
  gp-check-perm-ok p2 p1 p0 p2 ()
  gp-check-perm-ok p2 p1 p0 p3 _ = refl
  gp-check-perm-ok p2 p1 p1 p0 ()
  gp-check-perm-ok p2 p1 p1 p1 ()
  gp-check-perm-ok p2 p1 p1 p2 ()
  gp-check-perm-ok p2 p1 p1 p3 ()
  gp-check-perm-ok p2 p1 p2 p0 ()
  gp-check-perm-ok p2 p1 p2 p1 ()
  gp-check-perm-ok p2 p1 p2 p2 ()
  gp-check-perm-ok p2 p1 p2 p3 ()
  gp-check-perm-ok p2 p1 p3 p0 _ = refl
  gp-check-perm-ok p2 p1 p3 p1 ()
  gp-check-perm-ok p2 p1 p3 p2 ()
  gp-check-perm-ok p2 p1 p3 p3 ()
  gp-check-perm-ok p2 p2 p0 p0 ()
  gp-check-perm-ok p2 p2 p0 p1 ()
  gp-check-perm-ok p2 p2 p0 p2 ()
  gp-check-perm-ok p2 p2 p0 p3 ()
  gp-check-perm-ok p2 p2 p1 p0 ()
  gp-check-perm-ok p2 p2 p1 p1 ()
  gp-check-perm-ok p2 p2 p1 p2 ()
  gp-check-perm-ok p2 p2 p1 p3 ()
  gp-check-perm-ok p2 p2 p2 p0 ()
  gp-check-perm-ok p2 p2 p2 p1 ()
  gp-check-perm-ok p2 p2 p2 p2 ()
  gp-check-perm-ok p2 p2 p2 p3 ()
  gp-check-perm-ok p2 p2 p3 p0 ()
  gp-check-perm-ok p2 p2 p3 p1 ()
  gp-check-perm-ok p2 p2 p3 p2 ()
  gp-check-perm-ok p2 p2 p3 p3 ()
  gp-check-perm-ok p2 p3 p0 p0 ()
  gp-check-perm-ok p2 p3 p0 p1 _ = refl
  gp-check-perm-ok p2 p3 p0 p2 ()
  gp-check-perm-ok p2 p3 p0 p3 ()
  gp-check-perm-ok p2 p3 p1 p0 _ = refl
  gp-check-perm-ok p2 p3 p1 p1 ()
  gp-check-perm-ok p2 p3 p1 p2 ()
  gp-check-perm-ok p2 p3 p1 p3 ()
  gp-check-perm-ok p2 p3 p2 p0 ()
  gp-check-perm-ok p2 p3 p2 p1 ()
  gp-check-perm-ok p2 p3 p2 p2 ()
  gp-check-perm-ok p2 p3 p2 p3 ()
  gp-check-perm-ok p2 p3 p3 p0 ()
  gp-check-perm-ok p2 p3 p3 p1 ()
  gp-check-perm-ok p2 p3 p3 p2 ()
  gp-check-perm-ok p2 p3 p3 p3 ()
  gp-check-perm-ok p3 p0 p0 p0 ()
  gp-check-perm-ok p3 p0 p0 p1 ()
  gp-check-perm-ok p3 p0 p0 p2 ()
  gp-check-perm-ok p3 p0 p0 p3 ()
  gp-check-perm-ok p3 p0 p1 p0 ()
  gp-check-perm-ok p3 p0 p1 p1 ()
  gp-check-perm-ok p3 p0 p1 p2 _ = refl
  gp-check-perm-ok p3 p0 p1 p3 ()
  gp-check-perm-ok p3 p0 p2 p0 ()
  gp-check-perm-ok p3 p0 p2 p1 _ = refl
  gp-check-perm-ok p3 p0 p2 p2 ()
  gp-check-perm-ok p3 p0 p2 p3 ()
  gp-check-perm-ok p3 p0 p3 p0 ()
  gp-check-perm-ok p3 p0 p3 p1 ()
  gp-check-perm-ok p3 p0 p3 p2 ()
  gp-check-perm-ok p3 p0 p3 p3 ()
  gp-check-perm-ok p3 p1 p0 p0 ()
  gp-check-perm-ok p3 p1 p0 p1 ()
  gp-check-perm-ok p3 p1 p0 p2 _ = refl
  gp-check-perm-ok p3 p1 p0 p3 ()
  gp-check-perm-ok p3 p1 p1 p0 ()
  gp-check-perm-ok p3 p1 p1 p1 ()
  gp-check-perm-ok p3 p1 p1 p2 ()
  gp-check-perm-ok p3 p1 p1 p3 ()
  gp-check-perm-ok p3 p1 p2 p0 _ = refl
  gp-check-perm-ok p3 p1 p2 p1 ()
  gp-check-perm-ok p3 p1 p2 p2 ()
  gp-check-perm-ok p3 p1 p2 p3 ()
  gp-check-perm-ok p3 p1 p3 p0 ()
  gp-check-perm-ok p3 p1 p3 p1 ()
  gp-check-perm-ok p3 p1 p3 p2 ()
  gp-check-perm-ok p3 p1 p3 p3 ()
  gp-check-perm-ok p3 p2 p0 p0 ()
  gp-check-perm-ok p3 p2 p0 p1 _ = refl
  gp-check-perm-ok p3 p2 p0 p2 ()
  gp-check-perm-ok p3 p2 p0 p3 ()
  gp-check-perm-ok p3 p2 p1 p0 _ = refl
  gp-check-perm-ok p3 p2 p1 p1 ()
  gp-check-perm-ok p3 p2 p1 p2 ()
  gp-check-perm-ok p3 p2 p1 p3 ()
  gp-check-perm-ok p3 p2 p2 p0 ()
  gp-check-perm-ok p3 p2 p2 p1 ()
  gp-check-perm-ok p3 p2 p2 p2 ()
  gp-check-perm-ok p3 p2 p2 p3 ()
  gp-check-perm-ok p3 p2 p3 p0 ()
  gp-check-perm-ok p3 p2 p3 p1 ()
  gp-check-perm-ok p3 p2 p3 p2 ()
  gp-check-perm-ok p3 p2 p3 p3 ()
  gp-check-perm-ok p3 p3 p0 p0 ()
  gp-check-perm-ok p3 p3 p0 p1 ()
  gp-check-perm-ok p3 p3 p0 p2 ()
  gp-check-perm-ok p3 p3 p0 p3 ()
  gp-check-perm-ok p3 p3 p1 p0 ()
  gp-check-perm-ok p3 p3 p1 p1 ()
  gp-check-perm-ok p3 p3 p1 p2 ()
  gp-check-perm-ok p3 p3 p1 p3 ()
  gp-check-perm-ok p3 p3 p2 p0 ()
  gp-check-perm-ok p3 p3 p2 p1 ()
  gp-check-perm-ok p3 p3 p2 p2 ()
  gp-check-perm-ok p3 p3 p2 p3 ()
  gp-check-perm-ok p3 p3 p3 p0 ()
  gp-check-perm-ok p3 p3 p3 p1 ()
  gp-check-perm-ok p3 p3 p3 p2 ()
  gp-check-perm-ok p3 p3 p3 p3 ()

  gp-check-at : (t : Pos4) -> distinct4p t ≡ true -> gp-check-perm t ≡ true
  gp-check-at (a , b , c , d) h = gp-check-perm-ok a b c d h

-- gperm-of returns a circuit for every generalized permutation, and
-- that circuit implements it exactly with at most 9 gates, no K gate
-- and at most one CS gate.
gperm-of-gp-data : (G : GP) ->
                   Σ[ c ∈ Circuit ] ((gperm-of (gp-mat G) ≡ just c) × GPProps (gp-mat G) c)
gperm-of-gp-data G = c , gperm-of-gp-mat (gp-pos G) (gp-ph G) (gp-distinct G)
                   , gp-ok-props (gp-pos G) (gp-ph G) c chk
  where
    c : Circuit
    c = gperm-circuit-for (pos#4 (gp-pos G)) (ph#4 (gp-ph G))

    chk : gp-ok? (gp-pos G) (gp-ph G) c ≡ true
    chk = all-of-∈ (gp-check-phases (gp-pos G)) all-phase4
            (gp-check-at (gp-pos G) (gp-distinct G))
            (∈-all-phase4 (gp-ph G))
