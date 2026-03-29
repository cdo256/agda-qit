module QIT.Topology.Subset {ℓ ℓ'} where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset

𝓟 : (𝓤 : Set ℓ) → Set (ℓ ⊔ lsuc ℓ')
𝓟 𝓤 = 𝓤 → Prop ℓ'

∅ : ∀ {𝓤} → 𝓟 𝓤
∅ _ = ⊥p*
𝓤̇ : ∀ {𝓤} → 𝓟 𝓤
𝓤̇ _ = ⊤p*
_∪_ : ∀ {𝓤} → 𝓟 𝓤 → 𝓟 𝓤 → 𝓟 𝓤
(X ∪ Y) x = X x ∨ Y x
_∩_ : ∀ {𝓤} → 𝓟 𝓤 → 𝓟 𝓤 → 𝓟 𝓤
(X ∩ Y) x = X x ∧ Y x
⋃ : ∀ {𝓤} (I : Set) → (I → 𝓟 𝓤) → 𝓟 𝓤
⋃ I X x = ∃ λ i → X i x
⋂ : ∀ {𝓤} (I : Set) → (I → 𝓟 𝓤) → 𝓟 𝓤
⋂ I X x = ∀ i → X i x
