open import QIT.Prelude hiding (ℓD; lift)
open import QIT.Prop
open import QIT.Types
open import QIT.Setoid
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Container.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.QW.Subclasses using (DepthPreservingSig)
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Nullary
open import QIT.Relation.SetQuotient
open import QIT.Relation.Subset
open import QIT.Set.Bijection
open import QIT.Setoid.Quotient

module QIT.QW.Cocontinuity.ForW
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  ⦃ epo* : ExtensionalPlumpOrdinals ⦄
  where

private
  ℓD = ℓS ⊔ ℓP
  ℓD' = ℓS ⊔ ℓP

sig : Sig ℓS ℓP ℓ0 ℓ0
sig = W→Sig S P

instance
  depthPreserving* : DepthPreservingSig sig
  depthPreserving* = record { dpe = λ () }
  
open import QIT.QW.Cocontinuity.FromDepthPreservation

ψ = Cocontinuity.ψ
ϕ = Cocontinuity.ϕ
ψϕ = Cocontinuity.ψϕ
ϕψ = Cocontinuity.ϕψ
