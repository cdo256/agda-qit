open import QIT.Prelude

module QIT.Setoid.Algebra where

open import QIT.Setoid.Base
open import QIT.Setoid.Hom renaming (Hom to ≈Hom)
open import QIT.Setoid.Functor
open import Data.Product

module Alg {ℓX ℓX'} (F : Functor ℓX ℓX' ℓX ℓX') where
  open Functor F
  record Algebra : Set (lsuc ℓX ⊔ lsuc ℓX') where
    field
      X : Setoid ℓX ℓX'
      α : ≈Hom (F-ob X) X

    sup = α .≈Hom.to

  record Hom (Xα Yβ : Algebra) : Set (lsuc ℓX ⊔ lsuc ℓX') where
    open Algebra Xα
    open Algebra Yβ renaming (X to Y; α to β)
    field
      hom : ≈Hom X Y
      comm : (β ∘ F-mor hom) ≈h (hom ∘ α)
    
  record IsInitial (Xα : Algebra) : Set (lsuc ℓX ⊔ lsuc ℓX') where
    open Algebra Xα
    open Hom
    field
      rec : ∀ Yβ → Hom Xα Yβ
      unique : ∀ Yβ → (f : Hom Xα Yβ) → f .hom ≈h rec Yβ .hom

open Alg public using (Algebra)
