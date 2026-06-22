module QIT.Prelude.Axiom where

open import QIT.Prelude.Universe
open import QIT.Prelude.Logic
open import QIT.Prelude.Identity
open import QIT.Prelude.HLevel

PropExt : Propω
PropExt = ∀ {ℓA}
  → {A B : Prop ℓA}
  → A ⇔ B → A ≡ B

-- P∧Q→P≡Q : ∀ {ℓP} {P Q : Prop ℓP} → P ∧ Q → P ≡ Q
-- P∧Q→P≡Q (p , q) = propExt ((λ _ → q) , (λ _ → p))

A!C : Setω
A!C = ∀ {ℓX} (X : Set ℓX) → isContr X → X
