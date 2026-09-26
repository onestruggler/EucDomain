{-# OPTIONS --safe --without-K #-}

-- Complete canonical encoding of Gaussian integers modulo gamma cubed.
module Quantum.Synthesis.Ring.Properties.Gaussian.Gamma.Residue where

open import Quantum.Synthesis.Ring using (ZComplex; Cplx; _[i])
open import Instances as TC using (_+_; _-_; _*_; -_; 0#; 1#)
open _[i] using (re; im)
import Quantum.Synthesis.Ring.Properties.Gaussian.Gamma.Congruence as G
open import Finite.Check
open import Data.Integer using (ℤ; +_; _%ℕ_; _/ℕ_)
import Data.Integer as Z
import Data.Integer.DivMod as ZD
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Fin using (Fin; #_; toℕ; _≟_; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Vec.Base using (Vec; lookup; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

Code : Set
Code = Fin 8

decode : Code → ZComplex
decode c = lookup
  (Cplx (+ 0) (+ 0) ∷ Cplx (+ 1) (+ 0) ∷ Cplx (+ 1) (+ 1) ∷ Cplx (+ 2) (+ 1) ∷
   Cplx (+ 0) (+ 2) ∷ Cplx (+ 1) (+ 2) ∷ Cplx (+ 1) (+ 3) ∷ Cplx (+ 2) (+ 3) ∷ []) c

encodeTable : Vec (Vec Code 4) 4
encodeTable = ((# 0) ∷ (# 7) ∷ (# 4) ∷ (# 3) ∷ []) ∷
  ((# 1) ∷ (# 2) ∷ (# 5) ∷ (# 6) ∷ []) ∷
  ((# 4) ∷ (# 3) ∷ (# 0) ∷ (# 7) ∷ []) ∷
  ((# 5) ∷ (# 6) ∷ (# 1) ∷ (# 2) ∷ []) ∷ []

coordinateCode : ℤ → Fin 4
coordinateCode z = fromℕ< (ZD.n%ℕd<d z 4)

coordinate-value : ∀ z → toℕ (coordinateCode z) ≡ z %ℕ 4
coordinate-value z = toℕ-fromℕ< (ZD.n%ℕd<d z 4)

encodeSmall : Fin 4 → Fin 4 → Code
encodeSmall a b = lookup (lookup encodeTable a) b

encode : ZComplex → Code
encode z = encodeSmall (coordinateCode (re z)) (coordinateCode (im z))

reduce-four : ∀ z → G.Cong 3 z (Cplx (+ (re z %ℕ 4)) (+ (im z %ℕ 4)))
reduce-four (Cplx a b) = Cplx (qb Z.- qa) (Z.- qa Z.- qb) , cong₂ Cplx
  (trans (ZD.a≡a%ℕn+[a/ℕn]*n a 4)
    (solve 3 (λ x y r → r :+ x :* con (+ 4) := r :+ ((y :- x) :* con (Z.- (+ 2)) :- ((:- x) :- y) :* con (+ 2))) refl qa qb (+ (a %ℕ 4))))
  (trans (ZD.a≡a%ℕn+[a/ℕn]*n b 4)
    (solve 3 (λ x y r → r :+ y :* con (+ 4) := r :+ ((y :- x) :* con (+ 2) :+ ((:- x) :- y) :* con (Z.- (+ 2)))) refl qa qb (+ (b %ℕ 4))))
  where
  qa = a /ℕ 4
  qb = b /ℕ 4

abstract
  small-spec : ∀ a b → G.Cong 3 (Cplx (+ (toℕ a)) (+ (toℕ b))) (decode (encodeSmall a b))
  small-spec = checkFin 4 _ (λ a → decAll 4 _ (λ b → G.cong? 3 (Cplx (+ (toℕ a)) (+ (toℕ b))) (decode (encodeSmall a b)))) tt

encode-spec : ∀ z → G.Cong 3 z (decode (encode z))
encode-spec z = G.cong-trans 3 z (Cplx (+ (toℕ a)) (+ (toℕ b))) (decode (encode z))
  (subst (G.Cong 3 z) (cong₂ Cplx (cong +_ (sym (coordinate-value (re z)))) (cong +_ (sym (coordinate-value (im z))))) (reduce-four z))
  (small-spec a b)
  where
  a = coordinateCode (re z)
  b = coordinateCode (im z)

abstract
  decode-injective : ∀ a b → G.Cong 3 (decode a) (decode b) → a ≡ b
  decode-injective = checkFin 8 _ (λ a → decAll 8 _ (λ b → decImplies (G.cong? 3 (decode a) (decode b)) (a ≟ b))) tt

  encode-decode : ∀ c → encode (decode c) ≡ c
  encode-decode = checkFin 8 _ (λ c → encode (decode c) ≟ c) tt

encode-congruent : ∀ a b → G.Cong 3 a b → encode a ≡ encode b
encode-congruent a b h = decode-injective (encode a) (encode b)
  (G.cong-trans 3 (decode (encode a)) a (decode (encode b)) (G.cong-sym 3 a (decode (encode a)) (encode-spec a))
    (G.cong-trans 3 a b (decode (encode b)) h (encode-spec b)))

congruent-from-code : ∀ a b → encode a ≡ encode b → G.Cong 3 a b
congruent-from-code a b h = G.cong-trans 3 a (decode (encode b)) b
  (subst (λ c → G.Cong 3 a (decode c)) h (encode-spec a)) (G.cong-sym 3 b (decode (encode b)) (encode-spec b))

addCode multiplyCode : Code → Code → Code
addCode a b = encode (decode a + decode b)
multiplyCode a b = encode (decode a * decode b)

negateCode conjugateCode : Code → Code
negateCode a = encode (- decode a)
conjugateCode a = encode (TC.adj (decode a))

encode-add : ∀ a b → encode (a + b) ≡ addCode (encode a) (encode b)
encode-add a b = encode-congruent (a + b) (decode (encode a) + decode (encode b))
  (G.cong-add 3 a (decode (encode a)) b (decode (encode b)) (encode-spec a) (encode-spec b))

encode-mul : ∀ a b → encode (a * b) ≡ multiplyCode (encode a) (encode b)
encode-mul a b = encode-congruent (a * b) (decode (encode a) * decode (encode b))
  (G.cong-mul 3 a (decode (encode a)) b (decode (encode b)) (encode-spec a) (encode-spec b))

encode-conj : ∀ a → encode (TC.adj a) ≡ conjugateCode (encode a)
encode-conj a = encode-congruent (TC.adj a) (TC.adj (decode (encode a))) (G.cong-conj 3 a (decode (encode a)) (encode-spec a))

