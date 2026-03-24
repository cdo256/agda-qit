{-# OPTIONS --universe-polymorphism #-}
module QIT.Function.Base where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset

variable
  ℓA ℓB : Level

Surjective : ∀ {A : Set ℓA} {B : Set ℓB}
           → (A → B) → Prop _
Surjective f = ∀ y → ∃ λ x → f x ≡ y

Surjection : (A : Set ℓA) (B : Set ℓB) → Set _
Surjection A B = ΣP (A → B) Surjective

_↠_ = Surjection

-- Bijections between sets - one-to-one correspondences with explicit inverses.
module ↔ where
  record _↔_ {ℓX ℓY} (X : Set ℓX) (Y : Set ℓY) : Set (ℓX ⊔ ℓY) where
    field
      to : X → Y
      from : Y → X
      rinv : ∀ x → from (to x) ≡ x
      linv : ∀ y → to (from y) ≡ y

  open _↔_ public

  refl : {X : Set} → X ↔ X
  refl = record
    { to = λ x → x
    ; from = λ x → x
    ; rinv = λ _ → ≡.refl
    ; linv = λ _ → ≡.refl }

  flip : {X Y : Set} → X ↔ Y → Y ↔ X
  flip X↔Y = record
    { to = X↔Y .from
    ; from = X↔Y .to
    ; rinv = X↔Y .linv
    ; linv = X↔Y .rinv }
    where open _↔_ X↔Y

  _∘_ : {X Y Z : Set} → Y ↔ Z → X ↔ Y → X ↔ Z
  q ∘ p = record
    { to = λ x → q.to (p.to x)
    ; from = λ z → p.from (q.from z)
    ; rinv = λ x → ≡.trans (≡.cong p.from (q.rinv (p.to x))) (p.rinv x)
    ; linv = λ z → ≡.trans (≡.cong q.to (p.linv (q.from z))) (q.linv z) }
    where
    module p = _↔_ p
    module q = _↔_ q

open ↔ using (_↔_) public
