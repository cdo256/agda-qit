module QIT.Container where

open import QIT.Prelude
open import Data.Product

⟦_◁_⟧ : ∀ {ℓS ℓP ℓX} → (S : Set ℓS) (P : S → Set ℓP) → Set ℓX → Set (ℓS ⊔ ℓP ⊔ ℓX)
⟦ S ◁ P ⟧ X = Σ[ s ∈ S ] (P s → X)

module _ {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where
  data W : Set (ℓS ⊔ ℓP) where
    sup : ⟦ S ◁ P ⟧ W → W

  recW : ∀ {ℓX} {A : Set ℓX}
      → (r : ∀ s (f : (x : P s) → A) → A)
      → W → A
  recW r (sup (s , f)) = r s λ x → recW r (f x)
