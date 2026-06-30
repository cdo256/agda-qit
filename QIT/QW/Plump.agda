open import QIT.Prelude
open import QIT.QW.Signature
open import QIT.Plump.Algebra
import QIT.Plump.Properties

module QIT.QW.Plump
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  where

record ExtensionalPlumpOrdinals ℓA
  : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓA)
  where
  open Sig sig
  field
    Zᴬ : PlumpAlgebra S P ℓA ℓA ℓA

  open QIT.Plump.Properties Zᴬ

  field
    isExtensionalZᴬ : IsExtensional

  open IsExtensional isExtensionalZᴬ public
