open import QIT.Prelude
open import QIT.Prop
open import QIT.Setoid
open import QIT.Functor.Base
open import QIT.Category.Set
open import QIT.Relation.Binary

open import QIT.Container.Base

-- Define a setoid functor from a container (S ◁ P).
-- This lifts the container interpretation to work with setoids, creating
-- a functor that preserves equivalence relations. The resulting functor
-- maps setoids to setoids and homomorphisms to homomorphisms.
module QIT.Container.StrictFunctor {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓA : Level) where

-- The complete setoid functor induced by container (S ◁ P)
F : Functor (SetCat ℓA) (SetCat (ℓS ⊔ ℓP ⊔ ℓA))
F = record
  { ob = ⟦ S ◁ P ⟧
  ; hom = λ g (s , f) → s , (λ z → g (f z))
  ; id = ≡.refl
  ; comp = λ _ _ → ≡.refl 
  }
