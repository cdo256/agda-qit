open import QIT.Prelude
open import QIT.QW.Signature
open import QIT.Plump.Algebra
open import QIT.QW.Plump
open import QIT.Relation.SetQuotient

module QIT.QW.Cocontinuity 
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  where

import QIT.QW.Cocontinuity.FromDepthPreservation
