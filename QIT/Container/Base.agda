module QIT.Container.Base where

open import QIT.Prelude

⟦_◁_⟧ : ∀ {ℓS ℓP ℓX} → (S : Set ℓS) (P : S → Set ℓP) → Set ℓX → Set (ℓS ⊔ ℓP ⊔ ℓX)
⟦ S ◁ P ⟧ X = Σ[ s ∈ S ] (P s → X)

module _ {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where
  data W : Set (ℓS ⊔ ℓP) where
    sup : ⟦ S ◁ P ⟧ W → W

  recW : ∀ {ℓX} {X : Set ℓX}
      → (r : ∀ s (f : P s → X) → X)
      → W → X
  recW r (sup (s , f)) = r s λ i → recW r (f i)

module _ {ℓS ℓP ℓS' ℓP'} {S : Set ℓS} {S' : Set ℓS'} {P : S → Set ℓP} {P' : S' → Set ℓP'} where
  map : ∀ {ℓX} {X : Set ℓX} (fs : S → S') (fp : ∀ {s} → P' (fs s) → P s) → ⟦ S ◁ P ⟧ X → ⟦ S' ◁ P' ⟧ X
  map fs fp (s , f) = fs s , λ i → f (fp i)

  mapW : (fs : S → S') (fp : ∀ {s} → P' (fs s) → P s) → W S P → W S' P'
  mapW fs fp (sup (s , f)) = sup (fs s , λ i → mapW fs fp (f (fp i)))
