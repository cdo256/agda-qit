module QIT.Topology.Examples where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Topology.Subset
open import QIT.Topology.Base
open import QIT.Topology.BishopReals

∅ᵀ : Space ℓ0 ℓ0 (lsuc ℓ0)
∅ᵀ = FreeSpace {ℓ𝓞 = ℓ0} ⊥ 𝓤̇

∙ᵀ : Space ℓ0 ℓ0 (lsuc ℓ0)
∙ᵀ = FreeSpace {ℓ𝓞 = ℓ0} ⊤ 𝓤̇

ℝᵀ : Space ℓ0 ℓ0 (lsuc ℓ0)
ℝᵀ = FreeSpace {ℓ𝓞 = lsuc ℓ0} ℝ 𝓞ℝ
  module _ where
  data 𝓞ℝ : 𝓟 ℝ → Prop (lsuc ℓ0) where
    ball : ∀ x r → 𝓞ℝ (Ball x r)

𝕀 : ℝ → Prop
𝕀 = [ 0ℝ , 1ℝ ]

Iᵀ : Space ℓ0 ℓ0 (lsuc ℓ0)
Iᵀ = Restriction ℝᵀ 𝕀

Discreteᵀ : ∀ {ℓ} (X : Set ℓ) → Space ℓ ℓ (lsuc ℓ)
Discreteᵀ X = FreeSpace X λ _ → ⊤p

S¹ᵀ : Space _ _ _
S¹ᵀ = FreeSpace ⟨ Iᵀ ⟩ 𝓞S¹
  where
  open Space Iᵀ
  data 𝓞S¹ : 𝓟 𝓤 → Prop ℓ0 where
    
