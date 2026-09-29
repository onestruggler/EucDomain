{-# OPTIONS --safe --without-K #-}

-- 2×2 minors of a 4×4 matrix and their position and sign in the exterior
-- square (GauInt.Matrix.Exterior.pairs).
module GauInt.Matrix.Exterior.Minors where

open import Quantum.Synthesis.Ring using (ZComplex)
open import Instances as TC using (_-_; _*_; -_; 0#; 1#)
open import GauInt.Matrix using (Mat)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F)

minor : Mat 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ZComplex
minor M a k b j = M a b * M k j - M a j * M k b

pairIndex : Fin 4 → Fin 4 → Fin 6
pairIndex 0F 1F = 0F
pairIndex 1F 0F = 0F
pairIndex 0F 2F = 1F
pairIndex 2F 0F = 1F
pairIndex 0F 3F = 2F
pairIndex 3F 0F = 2F
pairIndex 1F 2F = 3F
pairIndex 2F 1F = 3F
pairIndex 1F 3F = 4F
pairIndex 3F 1F = 4F
pairIndex 2F 3F = 5F
pairIndex 3F 2F = 5F
pairIndex _ _ = 0F

pairSign : Fin 4 → Fin 4 → ZComplex
pairSign 0F 0F = 0#
pairSign 1F 1F = 0#
pairSign 2F 2F = 0#
pairSign 3F 3F = 0#
pairSign 0F _ = 1#
pairSign 1F 2F = 1#
pairSign 1F 3F = 1#
pairSign 2F 3F = 1#
pairSign _ _ = - 1#
