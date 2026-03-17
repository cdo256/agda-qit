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
