

```
open import QIT.Prelude
open import QIT.Setoid
∇ : Set → Setoid ℓ0 ℓ0
∇ X = X /≡

U : Setoid ℓ0 ℓ0 → Set
U X̃ = ⟨ X̃ ⟩
```

Then we should have

(X , ≡) → (Y , ~)
-----------------
      X → Y

/≈

```
ϕ : ∀ (X : Set) (Ỹ : Setoid ℓ0 ℓ0)
  → ≈.Hom (X /≡) Ỹ → (X → ⟨ Ỹ ⟩)
ϕ X Ỹ f = λ x → f.to x
  where
  module f = ≈.Hom f

ψ : ∀ (X : Set) (Ỹ : Setoid ℓ0 ℓ0)
  → (X → ⟨ Ỹ ⟩) → ≈.Hom (X /≡) Ỹ
ψ X Ỹ g = record
  { to = g
  ; cong = λ { reflp → refl } }
  where
  open Setoid Ỹ

linv : ∀ X Ỹ f → ψ X Ỹ (ϕ X Ỹ f) ≈h f 
linv X Ỹ f {x} = refl
  where 
  open Setoid Ỹ

rinv : ∀ X Ỹ g → ϕ X Ỹ (ψ X Ỹ g) ≡ g 
rinv X Ỹ g = ≡.refl
```
