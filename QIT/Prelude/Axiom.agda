module QIT.Prelude.Axiom where

open import QIT.Prelude.Universe
open import QIT.Prelude.Logic
open import QIT.Prelude.Identity
open import QIT.Prelude.HLevel

PropExt : Propω
PropExt = ∀ {ℓA} 
  → {A B : Prop ℓA}
  → A ⇔ B → A ≡ B

A!C : Agda.Primitive.Setω
A!C = ∀ {ℓX} (X : Set ℓX) → isContr X → X
