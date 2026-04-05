module QIT.Topology.Filtered where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Topology.Subset

private
  variable
    ℓ𝓤 ℓ𝓟 ℓ𝓞 : Level

record Filter {ℓ𝓤 ℓ𝓟 ℓ𝓞}
       (𝓤 : Set ℓ𝓤) (ℱ : 𝓟 ℓ𝓟 𝓤 → Prop ℓ𝓞)
     : Set (lsuc (ℓ𝓟 ⊔ ℓ𝓞) ⊔ ℓ𝓤)
       where
  field
    𝓤∈ℱ : ℱ 𝓤̇
    ∅∉ℱ : ℱ ∅ → ⊥
    ⊂∈ℱ : (X Y : 𝓟 ℓ𝓟 𝓤) → ℱ X → X ⊂ Y → ℱ Y
    ∩∈ℱ : (X Y : 𝓟 ℓ𝓟 𝓤) → ℱ X → ℱ Y → ℱ (X ∩ Y)

record Space (ℓ𝓤 ℓ𝓟 ℓ𝓞 : Level) : Set (lsuc (ℓ𝓤 ⊔ ℓ𝓟 ⊔ ℓ𝓞)) where
  field
    𝓤        : Set ℓ𝓤
    𝓝        : 𝓤 → 𝓟 ℓ𝓟 𝓤 → Prop ℓ𝓞
    isFilter : ∀ x → Filter 𝓤 (𝓝 x)
    pt∈𝓝     : ∀ x N → 𝓝 x N → N x
    core : ∀ x N → 𝓝 x N
         → ΣP (𝓟 ℓ𝓟 𝓤) λ M → 𝓝 x M ∧ (∀ y → M y → 𝓝 y N)

  open Filter public
  data 𝓞 : 𝓟 ℓ𝓟 𝓤 → Prop (ℓ𝓞 ⊔ ℓ𝓤 ⊔ lsuc ℓ𝓟) where
    ∅∈𝓞 : 𝓞 ∅
    𝓤∈𝓞 : 𝓞 𝓤̇
    ⋃∈𝓞    : (I : Set) (X : I → 𝓟 ℓ𝓟 𝓤)
              → (∀ i → 𝓞 (X i))
              → 𝓞 (⋃ I X)
    ∩∈𝓞    : (X Y : 𝓟 ℓ𝓟 𝓤)
              → 𝓞 X → 𝓞 Y
              → 𝓞 (X ∩ Y)
    core∈𝓞 : ∀ x N → (Nx : 𝓝 x N)
        → 𝓞 (fst (core x N Nx))
