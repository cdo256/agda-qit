open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.QW.Signature 
open import QIT.QW.Algebra

module QIT.QW.Initiality {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
open Sig sig

open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Setoid as ≈
open import QIT.Container.Base
open import QIT.Relation.Plump S P
open import QIT.Setoid.Diagram ≤p

open import QIT.QW.Colimit ≤p ℓS (lsuc ℓS) hiding (_≈ˡ_)
open import QIT.QW.Cocontinuity ≤p
open import QIT.QW.Stage sig

open import QIT.Container.Functor S P (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
open F-Ob

module F = ≈.Functor F
module D = Diagram D
module F∘D = Diagram (F ∘ᴰ D)
module _ (cocont : Cocontinuous {ℓD = ℓS ⊔ ℓP} {ℓD' = ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV} F D) where
