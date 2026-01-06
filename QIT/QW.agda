module QIT.QW where

open import QIT.Prelude
open import QIT.Container
open import QIT.SystemOfEquations

record QW ℓS ℓP ℓE ℓV : Set (lsuc ℓE ⊔ lsuc ℓV ⊔ lsuc ℓS ⊔ lsuc ℓP) where
  field
    S : Set ℓS
    P : S → Set ℓP
    Ξ : SysEq S P ℓE ℓV

  open SysEq Ξ public
