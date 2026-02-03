open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary

module QIT.Set.Base where

module ≡syntax {ℓ} {A : Set ℓ} where

  infix 1 begin_
  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin p = p

  infixr 2 step-≡
  step-≡ : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ q p = ≡.trans p q
  syntax step-≡ x q p = x ≡⟨ p ⟩ q

  infix 3 _∎
  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = ≡.refl

infixr 1 _∘_
_∘_ : ∀ {ℓA ℓB ℓC}
    → {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
    → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
