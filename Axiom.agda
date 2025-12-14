module Axiom where

open import Axiom.Extensionality.Propositional

postulate
  funExt : ∀ {ℓ ℓ'} → Extensionality ℓ ℓ'
