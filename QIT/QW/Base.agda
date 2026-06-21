open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Container.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Set.Bijection
open import QIT.QW.Signature
import QIT.Relation.SetQuotient as Quot

module QIT.QW.Cocontinuity {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (propExt : PropExt)
  (sq : Quot.SetQuotients)
  (sqe : Quot.SetQuotientsElim)
  where

open Sig sig

import QIT.Plump.Algebra as Plump
import QIT.Plump.W.Base as PlumpW
import QIT.QW.Stage sig propExt sq sqe as StageBase
import QIT.QW.StageColimit sig propExt sq sqe as StageColimitBase

module ZW = PlumpW S P
module ZAlg = Plump ZW.Sᶻ ZW.Pᶻ

module WithZ {ℓA} (ZA : ZAlg.Algebra ℓA) where

  private
    ℓD = ℓA ⊔ ℓS ⊔ ℓP
    ℓD' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

  open import QIT.Category.Morphism (SetCat (ℓD ⊔ ℓD'))

  module StageColimit = StageColimitBase.WithZ ZA

  open StageColimit public
  open import QIT.QW.Colimit propExt sq sqe ≤p ℓD ℓD' hiding (_≈ˡ_)

  private
    ℓc = ℓA ⊔ ℓS ⊔ ℓP
    ℓc' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

  Cocontinuous : (F : Functor (SetCat (ℓc ⊔ ℓc')) (SetCat (ℓc ⊔ ℓc'))) (D : Diagram/≈ ℓc ℓc')
                → Prop ℓc'
  Cocontinuous F D =
    Colim/≈ (F ∘ D) ≅ Functor.ob F (Colim/≈ D)
