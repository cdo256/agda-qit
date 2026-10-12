open import QIT.Prelude
open import QIT.QW.Signature
open import QIT.Plump.Algebra
open import QIT.Relation.SetQuotient
open import QIT.Function.Base
open import QIT.Functor.Base

module QIT.QW.Cocontinuity 
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (Zᴬ  : PlumpAlgebra (sig .Sig.S) (sig .Sig.P))
  where

open Sig sig

open import QIT.QW.Diagram sig Zᴬ

open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
module F = Functor F

  where

import QIT.QW.Cocontinuity.FromDepthPreservation
import QIT.QW.Cocontinuity.ForW
