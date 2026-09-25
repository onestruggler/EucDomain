{-# OPTIONS --safe --without-K #-}

-- Generic laws for the native column-major matrices.
-- Adapted from Kopt.Algebra.Linear at a0b62a0 on the v-office branch;
-- the scalar congruence layer stays in the existing ring property modules.
module Quantum.Synthesis.Matrix.Properties where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
import Algebra.Properties.Semiring.Sum as SumProps
open import Level using (0ℓ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base as V using (Vec; []; _∷_; lookup)
import Data.Vec.Functional as VF
import Data.Vec.Properties as VP
import Data.List.Base as L
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Instances hiding (_•)
open import Quantum.Synthesis.Matrix public using (Matrix; Matrix'; unMatrix; _·+·_; _·-·_; _·*·_; _scalarmult_; null-matrix;
  adjoint; matrix-transpose; matrix-map; matrix4x4; SemiRingMatrix; RingMatrix; AdjointMatrix; DecEqMatrix)
open import Quantum.Synthesis.Matrix using (vector-transpose)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo; module Laws)
import Quantum.Synthesis.Ring.Properties.Hom as Hom

private variable
  m n p q : ℕ
  A B : Set

------------------------------------------------------------------------
-- Entries (EucDomain stores a matrix as its list of columns)

infix 10 _⟪_,_⟫
_⟪_,_⟫ : Matrix m n A → Fin m → Fin n → A
M ⟪ i , j ⟫ = lookup (lookup (unMatrix M) j) i

tabulate : (Fin m → Fin n → A) → Matrix m n A
tabulate f = Matrix' (V.tabulate λ j → V.tabulate λ i → f i j)

tabulate-! : ∀ (f : Fin m → Fin n → A) i j → tabulate f ⟪ i , j ⟫ ≡ f i j
tabulate-! f i j = trans (cong (λ c → lookup c i) (VP.lookup∘tabulate _ j)) (VP.lookup∘tabulate _ i)

vec-ext : ∀ {u v : Vec A n} → (∀ i → lookup u i ≡ lookup v i) → u ≡ v
vec-ext {u = u} {v} h = trans (sym (VP.tabulate∘lookup u)) (trans (VP.tabulate-cong h) (VP.tabulate∘lookup v))

ext : ∀ {M N : Matrix m n A} → (∀ i j → M ⟪ i , j ⟫ ≡ N ⟪ i , j ⟫) → M ≡ N
ext {M = Matrix' a} {Matrix' b} h = cong Matrix' (vec-ext λ j → vec-ext λ i → h i j)

map-! : ∀ (f : A → B) (M : Matrix m n A) i j → matrix-map f M ⟪ i , j ⟫ ≡ f (M ⟪ i , j ⟫)
map-! f (Matrix' a) i j = trans (cong (λ c → lookup c i) (VP.lookup-map j (V.map f) a)) (VP.lookup-map i f (lookup a j))

transpose-! : ∀ (M : Matrix m n A) i j → matrix-transpose M ⟪ i , j ⟫ ≡ M ⟪ j , i ⟫
transpose-! (Matrix' a) i j = go a i j
  where
  go : ∀ {m n} (a : Vec (Vec A m) n) j i → lookup (lookup (vector-transpose a) i) j ≡ lookup (lookup a j) i
  go (c ∷ cs) zero i = cong (λ v → lookup v zero) (VP.lookup-zipWith _∷_ i c _)
  go (c ∷ cs) (suc j) i = trans (cong (λ v → lookup v (suc j)) (VP.lookup-zipWith _∷_ i c _)) (go cs j i)

------------------------------------------------------------------------
-- Operations over a ring

module _ {R : Set} {{_ : SemiRing R}} where

  sum : (Fin n → R) → R
  sum = VF.foldr _+_ 0#

  -- The Kronecker delta and the identity matrix.
  δ : Fin n → Fin n → R
  δ zero zero = 1#
  δ zero (suc _) = 0#
  δ (suc _) zero = 0#
  δ (suc i) (suc j) = δ i j

  𝕀 : Matrix n n R
  𝕀 = tabulate δ

module _ {R : Set} {{_ : Ring R}} where
  infixr 7 _·_
  _·_ : R → Matrix m n R → Matrix m n R
  _·_ = _scalarmult_

------------------------------------------------------------------------
-- Laws over a commutative ring

module Linear {R : Set} {{_ : Ring R}} (isCR : IsCommutativeRing _≡_ _+_ _*_ -_ 0# 1#) where

  CR : CommutativeRing 0ℓ 0ℓ
  CR = record { Carrier = R ; _≈_ = _≡_ ; _+_ = _+_ ; _*_ = _*_ ; -_ = -_ ; 0# = 0# ; 1# = 1# ; isCommutativeRing = isCR }
  module C = CommutativeRing CR
  private
    module Σ = SumProps C.semiring

  sum-cong : ∀ {f g : Fin n → R} → (∀ i → f i ≡ g i) → sum f ≡ sum g
  sum-cong = Σ.sum-cong-≗

  sum-0 : ∀ n → sum {R = R} {n = n} (λ _ → 0#) ≡ 0#
  sum-0 = Σ.sum-replicate-zero

  ∑-comm : ∀ (f : Fin m → Fin n → R) → sum (λ i → sum (f i)) ≡ sum (λ j → sum (λ i → f i j))
  ∑-comm = Σ.∑-comm

  ∑-+ : ∀ (f g : Fin n → R) → sum (λ i → f i + g i) ≡ sum f + sum g
  ∑-+ = Σ.∑-distrib-+

  *-sumˡ : ∀ x (f : Fin n → R) → x * sum f ≡ sum (λ i → x * f i)
  *-sumˡ = Σ.*-distribˡ-sum

  *-sumʳ : ∀ x (f : Fin n → R) → sum f * x ≡ sum (λ i → f i * x)
  *-sumʳ = Σ.*-distribʳ-sum

  -- The Kronecker delta.
  δ-sym : ∀ (i j : Fin n) → δ {R = R} i j ≡ δ j i
  δ-sym zero zero = refl
  δ-sym zero (suc j) = refl
  δ-sym (suc i) zero = refl
  δ-sym (suc i) (suc j) = δ-sym i j

  δ-self : ∀ (i : Fin n) → δ {R = R} i i ≡ 1#
  δ-self zero = refl
  δ-self (suc i) = δ-self i

  δ-other : ∀ (i j : Fin n) → i ≢ j → δ {R = R} i j ≡ 0#
  δ-other zero zero h = ⊥-elim (h refl)
  δ-other zero (suc j) h = refl
  δ-other (suc i) zero h = refl
  δ-other (suc i) (suc j) h = δ-other i j (λ e → h (cong suc e))

  sum-δ : ∀ (i : Fin n) (f : Fin n → R) → sum (λ k → δ i k * f k) ≡ f i
  sum-δ {suc n} zero f = begin
    1# * f zero + sum (λ k → 0# * f (suc k)) ≡⟨ cong₂ _+_ (C.*-identityˡ (f zero)) (trans (sum-cong {f = λ k → 0# * f (suc k)} λ k → C.zeroˡ (f (suc k))) (sum-0 n)) ⟩
    f zero + 0#                              ≡⟨ C.+-identityʳ _ ⟩
    f zero ∎
  sum-δ (suc i) f = trans (cong₂ _+_ (C.zeroˡ (f zero)) (sum-δ i (f ∘ suc))) (C.+-identityˡ (f (suc i)))

  sum-δʳ : ∀ (j : Fin n) (f : Fin n → R) → sum (λ k → f k * δ k j) ≡ f j
  sum-δʳ j f = trans (sum-cong λ k → trans (C.*-comm _ _) (cong (_* f k) (δ-sym k j))) (sum-δ j f)

  -- Entries of scalar multiples, sums, products and the identity.
  ·-! : ∀ x (M : Matrix m n R) i j → (x · M) ⟪ i , j ⟫ ≡ x * M ⟪ i , j ⟫
  ·-! x = map-! (x *_)

  +-! : ∀ (M N : Matrix m n R) i j → (M ·+· N) ⟪ i , j ⟫ ≡ M ⟪ i , j ⟫ + N ⟪ i , j ⟫
  +-! (Matrix' a) (Matrix' b) i j =
    trans (cong (λ c → lookup c i) (VP.lookup-zipWith _ j a b)) (VP.lookup-zipWith _+_ i (lookup a j) (lookup b j))

  𝕀-! : ∀ (i j : Fin n) → 𝕀 {R = R} ⟪ i , j ⟫ ≡ δ i j
  𝕀-! = tabulate-! δ

  private
    -- The column computed by EucDomain's product.
    col : Vec (Vec R m) n → Vec R n → Vec R m
    col a v = lookup (unMatrix (Matrix' a ·*· Matrix' (v ∷ []))) zero

    col-! : ∀ (a : Vec (Vec R m) n) v i → lookup (col a v) i ≡ sum (λ k → lookup (lookup a k) i * lookup v k)
    col-! [] [] i = VP.lookup-replicate i 0#
    col-! (h ∷ []) (k ∷ []) i = trans (VP.lookup-map i (k *_) h) (trans (C.*-comm _ _) (sym (C.+-identityʳ _)))
    col-! (h ∷ t@(_ ∷ _)) (k ∷ s) i = trans (VP.lookup-zipWith _+_ i (V.map (k *_) h) (col t s))
      (cong₂ _+_ (trans (VP.lookup-map i (k *_) h) (C.*-comm _ _)) (col-! t s i))

  *-! : ∀ (M : Matrix m n R) (N : Matrix n p R) i j → (M ·*· N) ⟪ i , j ⟫ ≡ sum (λ k → M ⟪ i , k ⟫ * N ⟪ k , j ⟫)
  *-! (Matrix' a) (Matrix' b) i j = trans (cong (λ c → lookup c i) (VP.lookup-map j _ b)) (col-! a (lookup b j) i)

  ------------------------------------------------------------------------
  -- Laws of products and scalars

  *-assoc : ∀ (L : Matrix m n R) (M : Matrix n p R) (N : Matrix p q R) → (L ·*· M) ·*· N ≡ L ·*· (M ·*· N)
  *-assoc L M N = ext λ i j → begin
    ((L ·*· M) ·*· N) ⟪ i , j ⟫                                     ≡⟨ *-! (L ·*· M) N i j ⟩
    sum (λ k → (L ·*· M) ⟪ i , k ⟫ * N ⟪ k , j ⟫)                     ≡⟨ sum-cong (λ k → trans (cong (_* _) (*-! L M i k)) (*-sumʳ (N ⟪ k , j ⟫) (λ l → L ⟪ i , l ⟫ * M ⟪ l , k ⟫))) ⟩
    sum (λ k → sum (λ l → L ⟪ i , l ⟫ * M ⟪ l , k ⟫ * N ⟪ k , j ⟫))   ≡⟨ ∑-comm (λ k l → L ⟪ i , l ⟫ * M ⟪ l , k ⟫ * N ⟪ k , j ⟫) ⟩
    sum (λ l → sum (λ k → L ⟪ i , l ⟫ * M ⟪ l , k ⟫ * N ⟪ k , j ⟫))   ≡⟨ sum-cong (λ l → trans (sum-cong λ k → C.*-assoc (L ⟪ i , l ⟫) (M ⟪ l , k ⟫) (N ⟪ k , j ⟫))
                                                                          (sym (*-sumˡ (L ⟪ i , l ⟫) (λ k → M ⟪ l , k ⟫ * N ⟪ k , j ⟫)))) ⟩
    sum (λ l → L ⟪ i , l ⟫ * sum (λ k → M ⟪ l , k ⟫ * N ⟪ k , j ⟫))   ≡⟨ sum-cong (λ l → cong (_ *_) (sym (*-! M N l j))) ⟩
    sum (λ l → L ⟪ i , l ⟫ * (M ·*· N) ⟪ l , j ⟫)                     ≡⟨ *-! L (M ·*· N) i j ⟨
    (L ·*· (M ·*· N)) ⟪ i , j ⟫ ∎

  *-identityˡ : ∀ (M : Matrix n m R) → 𝕀 ·*· M ≡ M
  *-identityˡ M = ext λ i j → trans (*-! 𝕀 M i j) (trans (sum-cong λ k → cong (_* _) (𝕀-! i k)) (sum-δ i (λ k → M ⟪ k , j ⟫)))

  *-identityʳ : ∀ (M : Matrix m n R) → M ·*· 𝕀 ≡ M
  *-identityʳ M = ext λ i j → trans (*-! M 𝕀 i j) (trans (sum-cong λ k → cong (_ *_) (𝕀-! k j)) (sum-δʳ j (λ k → M ⟪ i , k ⟫)))

  ·-assoc : ∀ x y (M : Matrix m n R) → x · y · M ≡ (x * y) · M
  ·-assoc x y M = ext λ i j → trans (·-! x (y · M) i j) (trans (cong (x *_) (·-! y M i j)) (trans (sym (C.*-assoc _ _ _)) (sym (·-! (x * y) M i j))))

  ·-identity : ∀ (M : Matrix m n R) → 1# · M ≡ M
  ·-identity M = ext λ i j → trans (·-! 1# M i j) (C.*-identityˡ _)

  ·-*ˡ : ∀ x (M : Matrix m n R) (N : Matrix n p R) → (x · M) ·*· N ≡ x · (M ·*· N)
  ·-*ˡ x M N = ext λ i j → begin
    ((x · M) ·*· N) ⟪ i , j ⟫                 ≡⟨ *-! (x · M) N i j ⟩
    sum (λ k → (x · M) ⟪ i , k ⟫ * N ⟪ k , j ⟫) ≡⟨ sum-cong (λ k → trans (cong (_* _) (·-! x M i k)) (C.*-assoc _ _ _)) ⟩
    sum (λ k → x * (M ⟪ i , k ⟫ * N ⟪ k , j ⟫)) ≡⟨ *-sumˡ x (λ k → M ⟪ i , k ⟫ * N ⟪ k , j ⟫) ⟨
    x * sum (λ k → M ⟪ i , k ⟫ * N ⟪ k , j ⟫)   ≡⟨ cong (x *_) (*-! M N i j) ⟨
    x * (M ·*· N) ⟪ i , j ⟫                   ≡⟨ ·-! x (M ·*· N) i j ⟨
    (x · (M ·*· N)) ⟪ i , j ⟫ ∎

  ·-*ʳ : ∀ x (M : Matrix m n R) (N : Matrix n p R) → M ·*· (x · N) ≡ x · (M ·*· N)
  ·-*ʳ x M N = ext λ i j → begin
    (M ·*· (x · N)) ⟪ i , j ⟫                 ≡⟨ *-! M (x · N) i j ⟩
    sum (λ k → M ⟪ i , k ⟫ * (x · N) ⟪ k , j ⟫) ≡⟨ sum-cong (λ k → trans (cong (_ *_) (·-! x N k j)) (exch _ x _)) ⟩
    sum (λ k → x * (M ⟪ i , k ⟫ * N ⟪ k , j ⟫)) ≡⟨ *-sumˡ x (λ k → M ⟪ i , k ⟫ * N ⟪ k , j ⟫) ⟨
    x * sum (λ k → M ⟪ i , k ⟫ * N ⟪ k , j ⟫)   ≡⟨ cong (x *_) (*-! M N i j) ⟨
    x * (M ·*· N) ⟪ i , j ⟫                   ≡⟨ ·-! x (M ·*· N) i j ⟨
    (x · (M ·*· N)) ⟪ i , j ⟫ ∎
    where
    exch : ∀ a b c → a * (b * c) ≡ b * (a * c)
    exch a b c = trans (sym (C.*-assoc a b c)) (trans (cong (_* c) (C.*-comm a b)) (C.*-assoc b a c))

  ·-* : ∀ x y (M : Matrix m n R) (N : Matrix n p R) → (x · M) ·*· (y · N) ≡ (x * y) · (M ·*· N)
  ·-* x y M N = trans (·-*ˡ x M (y · N)) (trans (cong (x ·_) (·-*ʳ y M N)) (·-assoc x y (M ·*· N)))

  -- A native left fold agrees with any reference semantics having the same
  -- identity and product step. Prove this before specializing the ring or
  -- expanding a concrete gate's entries.
  module Evaluation {G : Set} {d : ℕ}
    (gate : G → Matrix d d R) (semantics : L.List G → Matrix d d R)
    (base : semantics L.[] ≡ 𝕀)
    (step : ∀ g c → semantics (g L.∷ c) ≡ gate g ·*· semantics c) where

    fold-correct : ∀ c (A : Matrix d d R) →
      L.foldl (λ B g → B ·*· gate g) A c ≡ A ·*· semantics c
    fold-correct L.[] A = sym (trans (cong (A ·*·_) base) (*-identityʳ A))
    fold-correct (g L.∷ c) A = trans (fold-correct c (A ·*· gate g))
      (trans (*-assoc A (gate g) (semantics c)) (cong (A ·*·_) (sym (step g c))))

    correct : ∀ c → L.foldl (λ A g → A ·*· gate g) (semantics L.[]) c ≡ semantics c
    correct c = trans (fold-correct c (semantics L.[]))
      (trans (cong (_·*· semantics c) base) (*-identityˡ (semantics c)))

  ------------------------------------------------------------------------
  -- Adjoints, for an involutive conjugation

  module Conjugate {{_ : Adjoint R}} (ADJ : IsInvolutiveRingEndo {R} adj) where
    open IsInvolutiveRingEndo ADJ
    open Laws isCR (IsInvolutiveRingEndo.isRingEndo ADJ) using (f-0)

    †-! : ∀ (M : Matrix m n R) i j → adjoint M ⟪ i , j ⟫ ≡ adj (M ⟪ j , i ⟫)
    †-! (Matrix' a) i j = trans (transpose-! (Matrix' (V.map (V.map adj) a)) i j) (map-! adj (Matrix' a) j i)

    adj-sum : ∀ (f : Fin n → R) → adj (sum f) ≡ sum (adj ∘ f)
    adj-sum {zero} f = f-0
    adj-sum {suc n} f = trans (f-+ _ _) (cong (adj (f zero) +_) (adj-sum (f ∘ suc)))

    adj-δ : ∀ (i j : Fin n) → adj (δ {R = R} i j) ≡ δ i j
    adj-δ zero zero = f-1
    adj-δ zero (suc j) = f-0
    adj-δ (suc i) zero = f-0
    adj-δ (suc i) (suc j) = adj-δ i j

    †-* : ∀ (M : Matrix m n R) (N : Matrix n p R) → adjoint (M ·*· N) ≡ adjoint N ·*· adjoint M
    †-* M N = ext λ i j → begin
      adjoint (M ·*· N) ⟪ i , j ⟫                           ≡⟨ †-! (M ·*· N) i j ⟩
      adj ((M ·*· N) ⟪ j , i ⟫)                             ≡⟨ cong adj (*-! M N j i) ⟩
      adj (sum (λ k → M ⟪ j , k ⟫ * N ⟪ k , i ⟫))            ≡⟨ adj-sum (λ k → M ⟪ j , k ⟫ * N ⟪ k , i ⟫) ⟩
      sum (λ k → adj (M ⟪ j , k ⟫ * N ⟪ k , i ⟫))            ≡⟨ sum-cong (λ k → trans (f-* _ _) (trans (C.*-comm _ _) (sym (cong₂ _*_ (†-! N i k) (†-! M k j))))) ⟩
      sum (λ k → adjoint N ⟪ i , k ⟫ * adjoint M ⟪ k , j ⟫)  ≡⟨ *-! (adjoint N) (adjoint M) i j ⟨
      (adjoint N ·*· adjoint M) ⟪ i , j ⟫ ∎

    †-· : ∀ x (M : Matrix m n R) → adjoint (x · M) ≡ adj x · adjoint M
    †-· x M = ext λ i j → trans (†-! (x · M) i j) (trans (cong adj (·-! x M j i))
      (trans (f-* _ _) (trans (cong (adj x *_) (sym (†-! M i j))) (sym (·-! (adj x) (adjoint M) i j)))))

    †-† : ∀ (M : Matrix m n R) → adjoint (adjoint M) ≡ M
    †-† M = ext λ i j → trans (†-! (adjoint M) i j) (trans (cong adj (†-! M j i)) (involutive _))

    †-𝕀 : adjoint (𝕀 {R = R} {n = n}) ≡ 𝕀
    †-𝕀 = ext λ i j → trans (†-! 𝕀 i j) (trans (cong adj (𝕀-! j i)) (trans (adj-δ j i) (trans (δ-sym j i) (sym (𝕀-! i j)))))

    gram : Matrix m n R → Matrix m m R
    gram M = M ·*· adjoint M

    gram-scale : ∀ x (M : Matrix m n R) → gram (x · M) ≡ (x * adj x) · gram M
    gram-scale x M = trans (cong ((x · M) ·*·_) (†-· x M)) (·-* x (adj x) M (adjoint M))

-- A coefficient homomorphism preserves native matrix multiplication.
module Map {A B : Set} {{ra : Ring A}} {{rb : Ring B}}
  (la : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (lb : IsCommutativeRing (_≡_ {A = B}) _+_ _*_ -_ 0# 1#)
  {f : A → B} (F : Hom.IsRingHom f) where
  private
    module Source = Linear {R = A} {{ra}} la
    module Target = Linear {R = B} {{rb}} lb
    module F = Hom.IsRingHom F

  map-sum : ∀ (g : Fin n → A) → f (sum g) ≡ sum (f ∘ g)
  map-sum {zero} g = F.f-0
  map-sum {suc n} g = trans (F.f-+ (g zero) (sum (g ∘ suc)))
    (cong (f (g zero) +_) (map-sum (g ∘ suc)))

  map-product : ∀ (M : Matrix m n A) (N : Matrix n p A) →
    matrix-map f (M ·*· N) ≡ matrix-map f M ·*· matrix-map f N
  map-product M N = ext λ i j →
    trans (map-! f (M ·*· N) i j)
      (trans (cong f (Source.*-! M N i j))
        (trans (map-sum (λ k → M ⟪ i , k ⟫ * N ⟪ k , j ⟫))
          (trans (Target.sum-cong (λ k → trans (F.f-* (M ⟪ i , k ⟫) (N ⟪ k , j ⟫))
            (sym (cong₂ _*_ (map-! f M i k) (map-! f N k j)))))
            (sym (Target.*-! (matrix-map f M) (matrix-map f N) i j)))))

  map-delta : ∀ (i j : Fin n) → f (δ i j) ≡ δ i j
  map-delta zero zero = F.f-1
  map-delta zero (suc j) = F.f-0
  map-delta (suc i) zero = F.f-0
  map-delta (suc i) (suc j) = map-delta i j

  map-identity : matrix-map f (𝕀 {R = A} {n = n}) ≡ 𝕀 {R = B}
  map-identity = ext λ i j → trans (map-! f 𝕀 i j)
    (trans (cong f (Source.𝕀-! i j)) (trans (map-delta i j) (sym (Target.𝕀-! i j))))

  map-scale : ∀ x (M : Matrix m n A) → matrix-map f (x scalarmult M) ≡ f x scalarmult matrix-map f M
  map-scale x M = ext λ i j → trans (map-! f (x scalarmult M) i j)
    (trans (cong f (Source.·-! x M i j))
      (trans (F.f-* x (M ⟪ i , j ⟫))
        (trans (cong (f x *_) (sym (map-! f M i j))) (sym (Target.·-! (f x) (matrix-map f M) i j)))))

  module Conjugate {{aa : Adjoint A}} {{ab : Adjoint B}}
    (aAdj : IsInvolutiveRingEndo {A} adj) (bAdj : IsInvolutiveRingEndo {B} adj)
    (mapAdj : ∀ x → f (adj x) ≡ adj (f x)) where
    private
      module SA = Source.Conjugate aAdj
      module TA = Target.Conjugate bAdj

    map-adjoint : ∀ (M : Matrix m n A) → matrix-map f (adjoint M) ≡ adjoint (matrix-map f M)
    map-adjoint M = ext λ i j → trans (map-! f (adjoint M) i j)
      (trans (cong f (SA.†-! M i j))
        (trans (mapAdj (M ⟪ j , i ⟫))
          (trans (cong adj (sym (map-! f M j i))) (sym (TA.†-! (matrix-map f M) i j)))))

    map-gram : ∀ (M : Matrix m n A) → matrix-map f (SA.gram M) ≡ TA.gram (matrix-map f M)
    map-gram M = trans (map-product M (adjoint M)) (cong (matrix-map f M ·*·_) (map-adjoint M))
