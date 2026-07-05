open import QIT.Prelude
open import QIT.Prop

module QIT.Types
  ⦃ pathElim* : PathElim ⦄
  where

data Maybep {ℓ} (X : Prop ℓ) :  Prop ℓ where
  nothing : Maybep X
  just : X → Maybep X 

mapBox : {P : Prop ℓP} {Q : Prop ℓQ} → (P → Q) → Box P → Box Q
mapBox f (box x) = box (f x)

inj₁≢inj₂ : {A : Set ℓA} {B : Set ℓB} {x : A} {y : B} → inj₁ x ≢ inj₂ y
inj₁≢inj₂ ()

Σ-proj₂ : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
  {x y : Σ A B} (e : x ≡ y)
  → subst B (≡.cong proj₁ e) (x .proj₂) ≡ y .proj₂
Σ-proj₂ ≡.refl = subst-refl _
