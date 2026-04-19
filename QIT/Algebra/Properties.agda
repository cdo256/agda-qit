open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base hiding (sup)
open import QIT.Category.Base
open import QIT.Category.Set
open import QIT.Set.Base
open import QIT.Functor.Base
open import QIT.Algebra.Base

module QIT.Algebra.Properties where

Forget : ∀ {ℓS} → (F : Functor (SetCat ℓS) (SetCat ℓS))
       → Functor (AlgebraCategory F) (SetCat ℓS)
Forget F = record
  { ob = X
  ; hom = hom
  ; id = ≡.refl
  ; comp = λ _ _ → ≡.refl
  ; resp = λ p → p }
  where
  open Algebra
  open Hom
