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

Surjectiveˢ : ∀ {A : Set ℓA} {B : Set ℓB}
            → (A → B) → Set _
Surjectiveˢ f = ∀ y → Σ _ λ x → f x ≡ˢ y

Surjection : (A : Set ℓA) (B : Set ℓB) → Set _
Surjection A B = ΣP (A → B) Surjective

Surjectionˢ : (A : Set ℓA) (B : Set ℓB) → Set _
Surjectionˢ A B = Σ (A → B) Surjectiveˢ

_↠_ = Surjection
_↠ˢ_ = Surjectionˢ

-- Bijections between sets - one-to-one correspondences with explicit inverses.
module ↔ where
  record _↔_ {ℓX ℓY} (X : Set ℓX) (Y : Set ℓY) : Set (ℓX ⊔ ℓY) where
    field
      to : X → Y
      from : Y → X
      rinv : ∀ x → from (to x) ≡ x
      linv : ∀ y → to (from y) ≡ y

  open _↔_ public

  refl : ∀ {ℓX} {X : Set ℓX} → X ↔ X
  refl = record
    { to = λ x → x
    ; from = λ x → x
    ; rinv = λ _ → ≡.refl
    ; linv = λ _ → ≡.refl }

  flip : ∀ {ℓX ℓY} {X : Set ℓX} {Y : Set ℓY} → X ↔ Y → Y ↔ X
  flip X↔Y = record
    { to = X↔Y .from
    ; from = X↔Y .to
    ; rinv = X↔Y .linv
    ; linv = X↔Y .rinv }
    where open _↔_ X↔Y

  _∘_ : ∀ {ℓX ℓY ℓZ} {X : Set ℓX} {Y : Set ℓY} {Z : Set ℓZ} → Y ↔ Z → X ↔ Y → X ↔ Z
  q ∘ p = record
    { to = λ x → q.to (p.to x)
    ; from = λ z → p.from (q.from z)
    ; rinv = λ x → ≡.trans (≡.cong p.from (q.rinv (p.to x))) (p.rinv x)
    ; linv = λ z → ≡.trans (≡.cong q.to (p.linv (q.from z))) (q.linv z) }
    where
    module p = _↔_ p
    module q = _↔_ q

  open import QIT.Set.Bijection using (IsInjection)
  ↔to-Injection : ∀ {ℓX ℓY} {X : Set ℓX} {Y : Set ℓY}
                → (p : X ↔ Y) → IsInjection (p .to)
  ↔to-Injection {ℓX} {ℓY} {X} {Y} p {x} {y} q =
    ≡.trans (≡.sym (p .rinv x)) (≡.trans (≡.cong (p .from) q) (p .rinv y))

open ↔ using (_↔_; ↔to-Injection) public

module ↔ˢ where
  record _↔ˢ_ {ℓX ℓY} (X : Set ℓX) (Y : Set ℓY) : Set (ℓX ⊔ ℓY) where
    field
      to : X → Y
      from : Y → X
      rinv : ∀ x → from (to x) ≡ˢ x
      linv : ∀ y → to (from y) ≡ˢ y

  open _↔ˢ_ public

  refl : ∀ {ℓX} {X : Set ℓX} → X ↔ˢ X
  refl = record
    { to = λ x → x
    ; from = λ x → x
    ; rinv = λ _ → reflˢ
    ; linv = λ _ → reflˢ }

  flip : ∀ {ℓX ℓY} {X : Set ℓX} {Y : Set ℓY} → X ↔ˢ Y → Y ↔ˢ X
  flip X↔Y = record
    { to = X↔Y .from
    ; from = X↔Y .to
    ; rinv = X↔Y .linv
    ; linv = X↔Y .rinv }
    where open _↔ˢ_ X↔Y

  _∘_ : ∀ {ℓX ℓY ℓZ} {X : Set ℓX} {Y : Set ℓY} {Z : Set ℓZ} → Y ↔ˢ Z → X ↔ˢ Y → X ↔ˢ Z
  q ∘ p = record
    { to = λ x → q.to (p.to x)
    ; from = λ z → p.from (q.from z)
    ; rinv = λ x → transˢ (congˢ p.from (q.rinv (p.to x))) (p.rinv x)
    ; linv = λ z → transˢ (congˢ q.to (p.linv (q.from z))) (q.linv z) }
    where
    module p = _↔ˢ_ p
    module q = _↔ˢ_ q

module _ {ℓX ℓY} {X : Set ℓX} {Y : Set ℓY} where
  open ↔ˢ using (_↔ˢ_)
  open import QIT.Set.Bijection using (IsInjectionˢ)

  ↔ˢto-Injectionˢ : (p : X ↔ˢ Y) → IsInjectionˢ (p .↔ˢ.to)
  ↔ˢto-Injectionˢ p {x} {y} q =
    transˢ (symˢ (p .↔ˢ.rinv x)) (transˢ (congˢ (p .↔ˢ.from) q) (p .↔ˢ.rinv y))

module _ {ℓX ℓY} {X : Set ℓX} {Y : Set ℓY} where
  open ↔ˢ using (_↔ˢ_)
  ↔→↔ˢ : X ↔ Y → X ↔ˢ Y
  ↔→↔ˢ p = record
    { to = p .↔.to
    ; from = p .↔.from
    ; rinv = λ x → ≡→≡ˢ (p .↔.rinv x)
    ; linv = λ y → ≡→≡ˢ (p .↔.linv y) }

  ↔ˢ→↔ : X ↔ˢ Y → X ↔ Y
  ↔ˢ→↔ p = record
    { to = p .↔ˢ.to
    ; from = p .↔ˢ.from
    ; rinv = λ x → ≡ˢ→≡ (p .↔ˢ.rinv x)
    ; linv = λ y → ≡ˢ→≡ (p .↔ˢ.linv y) }

open ↔ˢ using (_↔ˢ_) public
