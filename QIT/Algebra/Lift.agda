open import QIT.Prelude
open import QIT.Prop

-- Module for creating adapter algebras that work with Container functors at higher universe levels
-- while keeping the same underlying carrier type. This allows reusing algebras defined at lower
-- levels in contexts requiring higher levels, avoiding --type-in-type.
--
-- The key insight: instead of lifting the carrier, we create an adapter that translates
-- between the low-level and high-level functor representations while preserving semantics.
module QIT.Algebra.Lift
  {ℓS ℓP : Level} (S : Set ℓS) (P : S → Set ℓP)
  (ℓV : Level)  -- The additional level we need to accommodate
  where

open import QIT.Algebra.Base
open import QIT.Container.StrictFunctor S P

LiftAlgebra : Algebra (F (ℓS ⊔ ℓP)) → Algebra ((F (ℓS ⊔ ℓP ⊔ ℓV)))
LiftAlgebra Xα = mkAlg (Lift ℓV X) λ (s , f) → lift (α (s , λ x → lower (f x)))
  where
  open Algebra Xα
