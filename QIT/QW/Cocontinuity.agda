open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary

-- Define cocontinuous functors: functors that preserve colimits.
-- A functor F is cocontinuous if F(colim D) ≅ colim(F ∘ D) for all diagrams D.
-- This property is crucial for showing that container functors preserve the
-- colimit construction used to build quotient inductive types.
module QIT.QW.Cocontinuity {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤) {ℓD ℓD' : Level} where

private
  ℓc = ℓI ⊔ ℓD
  ℓc' = ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD'

open import QIT.QW.Colimit ≤p ℓc ℓc'
open import QIT.Setoid.Diagram ≤p

-- A functor F is cocontinuous if it preserves colimits up to isomorphism.
-- This means F(colim P) ≅ colim(F ∘ P) for any diagram P.
-- Cocontinuity ensures that applying F doesn't interfere with the
-- colimit construction - the functor and colimit operations commute.
Cocontinuous : (F : ≈.Functor ℓc ℓc' ℓc ℓc') (D : ≈.Diagram ≤p ℓc ℓc')
              → Prop ℓc'
Cocontinuous F D =
  Colim (F ∘ᴰ D) ≅ F.F-ob (Colim D)
  where
  module F = ≈.Functor F
