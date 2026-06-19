module QIT.Prelude.Truncation where

open import QIT.Prelude.Universe

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓI ℓP ℓQ ℓX ℓY ℓZ : Level

data ∥_∥ {ℓA} (A : Set ℓA) : Prop ℓA where
  ∣_∣ : A → ∥ A ∥

Trunc₁ : {A : Set ℓA} {ℓB : Level} → (A → Set ℓB) → (A → Prop ℓB)
Trunc₁ R x = ∥ R x ∥

Trunc₂ : {A : Set ℓA} {ℓB : Level} → (A → A → Set ℓB) → (A → A → Prop ℓB)
Trunc₂ R x y = ∥ R x y ∥
