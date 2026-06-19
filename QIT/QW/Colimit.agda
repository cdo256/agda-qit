open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Set.Base
open import QIT.Functor.Base
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set

module QIT.QW.Colimit {ℓI} {ℓ≤}
  {I : Set ℓI}
  (propExt : PropExt)
  (≤p : Preorder I ℓ≤)
  (ℓD ℓD' : Level)
  (P : Functor (PreorderCat I ≤p) (SetCat (ℓD ⊔ ℓD')))
  where

open import QIT.QW.Colimit.Properties propExt ≤p ℓD ℓD' P public
