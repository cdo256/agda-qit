open import QIT.Prelude
open import QIT.Setoid.Base
open import QIT.Setoid.Hom
open import Data.Product

module QIT.Setoid.Sigma
  {ℓI} {ℓS} {ℓS'}
  (I : Set ℓI) (S : I → Setoid ℓS ℓS')
  where

  Carrier = Σ I λ i → ⟨ S i ⟩

  data _≈Σ_ : Carrier → Carrier → Set (ℓI ⊔ ℓS ⊔ ℓS') where
    ≈Σ, : ∀ {i j : I} (p : i ≡ j) {x : ⟨ S i ⟩} {y : ⟨ S j ⟩}
        → S j [ subst (λ i → ⟨ S i ⟩) p x ≈ y ]
        → (i , x) ≈Σ (j , y)
