module QIT.Category.Setoid where

open import QIT.Prelude
open import QIT.Category.Base
open import QIT.Setoid.Base
open import QIT.Setoid.Hom

SetoidCat : ∀ ℓA ℓ≈ → Category (lsuc ℓA ⊔ lsuc ℓ≈) (ℓA ⊔ ℓ≈) (ℓA ⊔ ℓ≈)
SetoidCat ℓA ℓ≈ = record
  { Obj = Setoid ℓA ℓ≈
  ; _⇒_ = Hom
  ; _≈_ = _≈h_
  ; id = idHom
  ; _∘_ = _∘_
  ; assoc = λ {f = f} {g} {h} → ∘-assoc h g f
  ; sym-assoc = λ {A B C D} {f = f} {g} {h}
    → ≈h-sym {f = (h ∘ g) ∘ f} {g = h ∘ (g ∘ f)} (∘-assoc h g f)
  ; identityˡ = λ {f = f} → ≈h-refl {f = f}
  ; identityʳ = λ {f = f} → ≈h-refl {f = f}
  ; identity² = λ {A} → ≈h-refl {f = idHom {S = A}}
  ; equiv = ≈h-isEquivalence
  ; ∘-resp-≈ = λ {f = g₁} {g₂} {f₁} {f₂}
    → ∘-resp-≈ {g₁ = g₁} {g₂ = g₂} {f₁ = f₁} {f₂ = f₂}
  }
