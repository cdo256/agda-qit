{-# OPTIONS --type-in-type #-}
open import QIT.Prelude
open import QIT.Setoid
import QIT.Colimit as Colimit
open import QIT.Relation.Base
open import QIT.Relation.Binary

module QIT.Cocontinuity {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤) where

open import QIT.Diagram ≤p
open import QIT.Colimit ≤p
open import Data.Product

Cocontinuous : ∀ {ℓF ℓF'} → (F : ≈.Functor ℓF ℓF') (P : Diagram) → Prop lzero
Cocontinuous F P = Colim (F ∘ P) ≅ F.F-ob (Colim P)
  where
  module F = ≈.Functor F
