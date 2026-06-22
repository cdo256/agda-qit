open import QIT.Prelude
open import QIT.Prelude.Identity

module QIT.Logic where

open import QIT.Prelude.Logic public

⊥e' : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
⊥e' ()

⊥e : ∀ {ℓ} {A : Prop ℓ} → ⊥ → A
⊥e ()

⊥→⊥p : ⊥ˢ → ⊥
⊥→⊥p ()

_≢_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Prop ℓ
x ≢ y = ¬ (x ≡ y)

⇔refl : ∀ {ℓA} {A : Prop ℓA} → A ⇔ A
⇔refl = ∧i (λ z → z) (λ z → z)

⇔sym : ∀ {ℓA ℓB} {A : Prop ℓA} {B : Prop ℓB} → A ⇔ B → B ⇔ A
⇔sym (∧i p₁ p₂) = ∧i p₂ p₁

⇔trans : ∀ {ℓA ℓB ℓC} {A : Prop ℓA} {B : Prop ℓB} {C : Prop ℓC}
     → A ⇔ B → B ⇔ C → A ⇔ C
⇔trans (∧i p₁ p₂) (∧i q₁ q₂) = ∧i (λ z → q₁ (p₁ z)) (λ z → p₂ (q₂ z))
