open import QIT.Prelude
open import QIT.Setoid
open import QIT.Container.Base
open import QIT.QW.Equation 

-- Define signatures for quotient inductive types (QITs).
-- A signature specifies both the constructors (via a container) and
-- the equations that should hold in the quotient. This extends ordinary
-- inductive type signatures with equational constraints.
-- This definition follows closely the one defined in Fiore et al. 2022.
module QIT.QW.Signature where

private
  variable
    ℓS ℓP ℓE ℓV : Level

-- A QW signature consists of:
-- - (S, P): container specifying constructors and their arities
-- - E: set of equation names
-- - Ξ: assigns each equation name an actual equation over the constructors
--
-- This separates the "syntax" (constructors) from the "semantics" (equations),
-- allowing flexible specification of quotient inductive types.
record Sig ℓS ℓP ℓE ℓV : Set (lsuc ℓE ⊔ lsuc ℓV ⊔ lsuc ℓS ⊔ lsuc ℓP) where
  field
    -- Container signature: shapes (constructors) and positions (arguments)
    S : Set ℓS
    P : S → Set ℓP

    -- Equation signature: equation names and their interpretations
    E : Set ℓE
    Ξ : E → Equation S P ℓV

  open Equation public
