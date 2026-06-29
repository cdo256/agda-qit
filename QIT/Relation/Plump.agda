open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary
open import QIT.Container.Base

module QIT.Relation.Plump
  ⦃ pathElim* : PathElim ⦄
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  where

open import QIT.Plump.W.Base S P public
