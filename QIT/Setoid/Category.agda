module QIT.Setoid.Category where

open import QIT.Prelude
open import QIT.Category.Base
open import QIT.Setoid hiding (Setoid)

SetoidCat : ∀ ℓA ℓ≈ → Category (lsuc ℓA ⊔ lsuc ℓ≈) (ℓA ⊔ ℓ≈) (ℓA ⊔ ℓ≈)
SetoidCat ℓA ℓ≈ = record
  { Obj = ≈.Setoid ℓA ℓ≈
  ; _⇒_ = ≈.Hom
  ; _≈_ = _≈h_
  ; id = ≈.idHom
  ; _∘_ = ≈._∘_
  ; assoc = λ {f = f} {g} {h} → ≈.∘-assoc h g f
  ; sym-assoc = λ {A B C D} {f = f} {g} {h} {x} →
    ≈.≈h-sym {f = (h ≈.∘ g) ≈.∘ f} {g = h ≈.∘ (g ≈.∘ f)} (≈.∘-assoc h g f)
  ; identityˡ = λ {f = f} → ≈.≈h-refl {f = f}
  ; identityʳ = λ {f = f} → ≈.≈h-refl {f = f}
  ; identity² = λ {A} → ≈.≈h-refl {f = ≈.idHom {S = A}}
  ; equiv = ≈.≈h-isEquivalence
  ; ∘-resp-≈ = λ {A = A} {B} {C} {f₁} {f₂} {g₁} {g₂} → ≈.∘-resp-≈ {g₁ = f₁} {g₂ = f₂} {f₁ = g₁} {f₂ = g₂}
  }
