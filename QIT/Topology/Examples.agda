module QIT.Topology.Examples where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Topology.Subset
open import QIT.Topology.Base
open import QIT.Topology.BishopReals
open import QIT.Topology.Constructions

∅ᵀ : Space ℓ0 ℓ0 (lsuc ℓ0)
∅ᵀ = FreeSpace ℓ0 ⊥ 𝓤̇

∙ᵀ : Space ℓ0 ℓ0 (lsuc ℓ0)
∙ᵀ = FreeSpace ℓ0 ⊤ 𝓤̇

Discreteᵀ : ∀ {ℓ} (X : Set ℓ) → Space ℓ ℓ (lsuc ℓ)
Discreteᵀ X = FreeSpace _ X (λ _ → ⊤p)

ℝᵀ : Space ℓ0 ℓ0 (lsuc ℓ0)
ℝᵀ = FreeSpace _ ℝ 𝓞ℝ
  where
  data 𝓞ℝ : 𝓟 ℓ0 ℝ → Prop (lsuc ℓ0) where
    ball : ∀ x r → 𝓞ℝ (Ball x r)

𝕀 : 𝓟 _ ℝ
𝕀 = [ 0ℝ , 1ℝ ]

I : Space _ _ _
I = Restriction ℝᵀ 𝕀

module I = Space I

∂I : 𝓟 _ I.𝓤
∂I (x , _) = (x ≡ 0ℝ) ∨ (x ≡ 1ℝ)

-- Alternative definition as a space rather than a subset.
∂Iᵀ : Space _ _ _
∂Iᵀ = Restriction I λ (x , _) → (x ≡ 0ℝ) ∨ (x ≡ 1ℝ)

S¹ : Space _ _ _
S¹ = I /ᵀ ∂I

T² : Space _ _ _
T² = S¹ ⊓ᵀ S¹
