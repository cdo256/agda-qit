-- Basic foundations
open import QIT.Prelude hiding (ℓD)
open import QIT.Prop
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Setoid
open import QIT.Relation.SetQuotient
open import QIT.QW.Signature

-- Colimit construction for the staged diagram D used in building quotient W-types.
-- The colimit represents the "completion" of approximations built through plump
-- ordinal stages, providing a constructive way to build infinite quotient structures.
module QIT.QW.StageColimit
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  where

open Sig sig

import QIT.Plump.Algebra as Plump
import QIT.Plump.W.Base as PlumpW
import QIT.QW.Stage sig as Stage

module ZW = PlumpW S P
module ZAlg = Plump ZW.Sᶻ ZW.Pᶻ

module WithZ {ℓA} (ZA : ZAlg.Algebra ℓA) where

  private
    ℓD = ℓA ⊔ ℓS ⊔ ℓP
    ℓD' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV

  -- Container functor
  open import QIT.Container.Base
  open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
  open import QIT.Setoid.Quotient using (_/≈)

  module S = Stage.WithZ ZA
  open S public
  open S.Z public
  open import QIT.QW.Algebra sig

  -- Colimits and cocontinuity
  open import QIT.QW.Colimit Z.≤p ℓD ℓD' hiding (_≈ˡ_)

  -- Module aliases for cleaner notation
  module F = Functor F
  module D = Functor D
  module F∘D = Functor (F ∘ D)

  -- The underlying W-type of trees before quotienting.
  T = W S P

  -- Extract the stage index from a colimit element.
  αˡ : ⟨ Colim D ⟩ → Z
  αˡ (α , t̂) = α

  -- Extract the underlying tree from a colimit element.
  tˡ : (x : ⟨ Colim D ⟩) → D̃ (αˡ x) /≈
  tˡ (α , t̂) = t̂
