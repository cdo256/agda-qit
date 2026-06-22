module QIT.Function.Base where

open import QIT.Prelude
open import QIT.Prop

Surjective : ∀ {A : Set ℓA} {B : Set ℓB}
           → (A → B) → Prop _
Surjective f = ∀ y → ∃ λ x → f x ≡ y

Surjection : (A : Set ℓA) (B : Set ℓB) → Set _
Surjection A B = ΣP (A → B) Surjective

_↠_ = Surjection

-- Bijections between sets - one-to-one correspondences with explicit inverses.
module ≅ˢ where
  record _≅ˢ_ (X : Set ℓX) (Y : Set ℓY) : Set (ℓX ⊔ ℓY) where
    field
      to : X → Y
      from : Y → X
      rinv : ∀ x → from (to x) ≡ x
      linv : ∀ y → to (from y) ≡ y

  open _≅ˢ_ public

  refl : {X : Set ℓX} → X ≅ˢ X
  refl = record
    { to = λ x → x
    ; from = λ x → x
    ; rinv = λ _ → ≡.refl
    ; linv = λ _ → ≡.refl }

  sym : {X : Set ℓX} {Y : Set ℓY} → X ≅ˢ Y → Y ≅ˢ X
  sym X≅Y = record
    { to = X≅Y .from
    ; from = X≅Y .to
    ; rinv = X≅Y .linv
    ; linv = X≅Y .rinv }
    where open _≅ˢ_ X≅Y

  _∘_ : {X : Set ℓX} {Y : Set ℓY} {Z : Set ℓZ} → Y ≅ˢ Z → X ≅ˢ Y → X ≅ˢ Z
  q ∘ p = record
    { to = λ x → q.to (p.to x)
    ; from = λ z → p.from (q.from z)
    ; rinv = λ x → ≡.trans (≡.cong p.from (q.rinv (p.to x))) (p.rinv x)
    ; linv = λ z → ≡.trans (≡.cong q.to (p.linv (q.from z))) (q.linv z) }
    where
    module p = _≅ˢ_ p
    module q = _≅ˢ_ q

open ≅ˢ using (_≅ˢ_) public
