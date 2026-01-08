module QIT.QW.Signature where

open import QIT.Prelude
open import QIT.Setoid
open import QIT.Container.Base
open import QIT.QW.Equation

private
  variable
    ℓS ℓP ℓE ℓV : Level

record Sig ℓS ℓP ℓE ℓV : Set (lsuc ℓE ⊔ lsuc ℓV ⊔ lsuc ℓS ⊔ lsuc ℓP) where
  field
    S : Set ℓS
    P : S → Set ℓP
    E : Set ℓE
    Ξ : E → Equation S P ℓV

  open Equation public

