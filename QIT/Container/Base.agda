open import QIT.Prelude

module QIT.Container.Base where

-- Container interpretation: ⟦ S ◁ P ⟧ X represents the functor action.
-- An element consists of a shape s : S and a function P s → X assigning
-- elements of X to each position. This is the polynomial functor interpretation.
--
-- Example: For lists, S = ℕ (length) and P n = Fin n (positions).
-- Then ⟦ S ◁ P ⟧ X = Σ n. (Fin n → X) ≅ List X.
⟦_◁_⟧ : ∀ {ℓS ℓP ℓX} → (S : Set ℓS) (P : S → Set ℓP) → Set ℓX → Set (ℓS ⊔ ℓP ⊔ ℓX)
⟦ S ◁ P ⟧ X = Σ[ s ∈ S ] (P s → X)

module _ {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where
  -- W-types: well-founded trees with shapes S and branching P.
  -- This is the initial algebra for the container functor ⟦ S ◁ P ⟧.
  -- W S P represents trees where each node has shape s and P s many children.
  data W : Set (ℓS ⊔ ℓP) where
    sup : ⟦ S ◁ P ⟧ W → W
