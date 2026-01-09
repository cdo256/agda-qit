open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary

module QIT.QW.Cocontinuity {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤) where

module _ {ℓD ℓD' : Level} where
  private
    ℓc = ℓI ⊔ ℓD
    ℓc' = ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD'

  open import QIT.QW.Diagram ≤p
  open import QIT.QW.Colimit ≤p ℓc ℓc'

  Cocontinuous : (F : ≈.Functor ℓc ℓc' ℓc ℓc') (P : Diagram ℓc ℓc') → Prop ℓc'
  Cocontinuous F P =
    Colim (F ∘ P) ≅ F.F-ob (Colim P)
    where
    module F = ≈.Functor F
