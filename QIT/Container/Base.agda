open import QIT.Prelude

-- Define containers and their interpretations as functors and W-types.
-- A container (S ◁ P) consists of shapes S and positions P s for each shape.
-- This gives a systematic way to represent polynomial functors and their
-- corresponding inductive types (W-types).
--
-- Containers are fundamental for describing data structures: S represents
-- the "constructors" and P s represents the "arguments" for constructor s.
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

  -- Recursor for W-types: fold over the tree structure.
  -- Given a way to combine a shape s with results from P s many subtrees,
  -- produce a result for the entire tree. This implements structural recursion.
  recW : ∀ {ℓX} {X : Set ℓX}
      → (r : ∀ s (f : P s → X) → X)
      → W → X
  recW r (sup (s , f)) = r s λ i → recW r (f i)

-- Container morphisms: natural transformations between container functors.
-- A morphism (fs, fp) : (S ◁ P) → (S' ◁ P') maps shapes and positions
-- contravariantly, inducing a natural transformation ⟦ S ◁ P ⟧ → ⟦ S' ◁ P' ⟧.
module _ {ℓS ℓP ℓS' ℓP'} {S : Set ℓS} {S' : Set ℓS'} {P : S → Set ℓP} {P' : S' → Set ℓP'} where
  -- Map container interpretation: transform shapes forward, positions backward
  map : ∀ {ℓX} {X : Set ℓX} (fs : S → S') (fp : ∀ {s} → P' (fs s) → P s) → ⟦ S ◁ P ⟧ X → ⟦ S' ◁ P' ⟧ X
  map fs fp (s , f) = fs s , λ i → f (fp i)

  -- Induced map on W-types: container morphisms extend to W-type morphisms
  mapW : (fs : S → S') (fp : ∀ {s} → P' (fs s) → P s) → W S P → W S' P'
  mapW fs fp (sup (s , f)) = sup (fs s , λ i → mapW fs fp (f (fp i)))
