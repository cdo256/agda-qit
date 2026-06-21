module Logic.Prelude.Axiom where

open import Logic.Prelude.Universe
open import Logic.Prelude.Logic
open import Logic.Prelude.Identity
open import Logic.Prelude.HLevel

PropExt : Propω
PropExt = ∀ {ℓA} 
  → {A B : Prop ℓA}
  → A ⇔ B → A ≡ B

-- P∧Q→P≡Q : ∀ {ℓP} {P Q : Prop ℓP} → P ∧ Q → P ≡ Q
-- P∧Q→P≡Q (p , q) = propExt ((λ _ → q) , (λ _ → p))

A!C : Agda.Primitive.Setω
A!C = ∀ {ℓX} (X : Set ℓX) → isContr X → X

