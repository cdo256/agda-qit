open import QIT.Prelude
open import QIT.Prelude.Identity

module QIT.Logic where

open import QIT.Prelude.Logic public

absurdp : ∀ {ℓ} {A : Set ℓ} → ⊥p → A
absurdp ()

absurdp' : ∀ {ℓ} {A : Prop ℓ} → ⊥p → A
absurdp' ()

⊥→⊥p : ⊥ → ⊥p
⊥→⊥p ()

_≢_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Prop ℓ
x ≢ y = ¬ (x ≡ y)

⇔refl : ∀ {ℓA} {A : Prop ℓA} → A ⇔ A
⇔refl = (λ z → z) , (λ z → z)

⇔sym : ∀ {ℓA ℓB} {A : Prop ℓA} {B : Prop ℓB} → A ⇔ B → B ⇔ A
⇔sym (p₁ , p₂) = p₂ , p₁

⇔trans : ∀ {ℓA ℓB ℓC} {A : Prop ℓA} {B : Prop ℓB} {C : Prop ℓC}
     → A ⇔ B → B ⇔ C → A ⇔ C
⇔trans (p₁ , p₂) (q₁ , q₂) = (λ z → q₁ (p₁ z)) , (λ z → p₂ (q₂ z))
