{-# OPTIONS --type-in-type #-}

open import Prelude
open import Setoid.Base
open import Setoid.Hom
open import Data.Product

module Setoid.Sigma
  {ℓI} {ℓS} {ℓS'}
  (I : Set ℓI) (S : I → Setoid ℓS ℓS')
  where

  Carrier = Σ I λ i → ⟨ S i ⟩

  data _≈Σ_ : Carrier → Carrier → Set where
    ≈Σ, : ∀ {i j : I} (p : i ≡ j) {x : ⟨ S i ⟩} {y : ⟨ S j ⟩}
        → S j [ subst (λ i → ⟨ S i ⟩) p x ≈ y ]
        → (i , x) ≈Σ (j , y)
