{-# OPTIONS --type-in-type #-}
module QIT.Topology.Base where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Topology.Subset

record Space ℓ𝓤 ℓ𝓟 ℓ𝓞 : Set (lsuc (ℓ𝓤 ⊔ ℓ𝓟 ⊔ ℓ𝓞)) where
  field
    𝓤 : Set ℓ𝓤
    𝓞 : 𝓟 {ℓ' = ℓ𝓟} 𝓤 → Prop ℓ𝓞
    ∅∈𝓞 : 𝓞 ∅
    𝓤∈𝓞 : 𝓞 𝓤̇ 
    ⋃∈𝓞 : (I : Set) (X : I → 𝓟 𝓤)
        → (∀ i → 𝓞 (X i))
        → 𝓞 (⋃ I X)
    ∩∈𝓞 : (X Y : 𝓟 𝓤)
        → 𝓞 X → 𝓞 Y
        → 𝓞 (X ∩ Y)

module _ {ℓ𝓤 ℓ𝓟 ℓ𝓞} where
  ⟨_⟩ : (Space ℓ𝓤 ℓ𝓟 ℓ𝓞) → Set ℓ𝓤
  ⟨ A ⟩ = A .Space.𝓤

  -- Freely generated open sets
  data 𝓞[_]  {𝓤 : Set ℓ𝓤}
          (𝓞 : 𝓟 {ℓ' = ℓ𝓟} 𝓤 → Prop ℓ𝓞)
      : 𝓟 {ℓ' = ℓ𝓟} 𝓤
      → Prop (ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞) where
    𝓞∈[𝓞] : ∀ X → 𝓞 X → 𝓞[ 𝓞 ] X
    ∅∈[𝓞] : 𝓞[ 𝓞 ] ∅
    𝓤∈[𝓞] : 𝓞[ 𝓞 ] 𝓤̇
    ⋃∈[𝓞] : (I : Set) (X : I → 𝓟 𝓤)
        → (∀ i → 𝓞[ 𝓞 ] (X i))
        → 𝓞[ 𝓞 ] (⋃ I X)
    ∩∈[𝓞] : (X Y : 𝓟 𝓤)
        → 𝓞[ 𝓞 ] X → 𝓞[ 𝓞 ] Y
        → 𝓞[ 𝓞 ] (X ∩ Y)

  FreeSpace : 
            (𝓤 : Set ℓ𝓤)
          → (𝓞 : 𝓟 {ℓ' = ℓ𝓟} 𝓤 → Prop ℓ𝓞)
          → Space ℓ𝓤 ℓ𝓟 (ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞)
  FreeSpace 𝓤 𝓞 = record
    { 𝓤 = 𝓤
    ; 𝓞 = 𝓞[ 𝓞 ]
    ; ∅∈𝓞 = ∅∈[𝓞]
    ; 𝓤∈𝓞 = 𝓤∈[𝓞]
    ; ⋃∈𝓞 = ⋃∈[𝓞]
    ; ∩∈𝓞 = ∩∈[𝓞] }

  -- Continuous function
  record _⇒_ (A B : Space ℓ𝓤 ℓ𝓟 ℓ𝓞) : Set (ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞) where
    constructor _,_
    module A = Space A
    module B = Space B
    field
      f : A.𝓤 → B.𝓤
      -- Y open → f⁻¹ Y open
      f𝓞 : ∀ Y → B.𝓞 Y → A.𝓞 λ x → Y (f x) 

  Restriction
    : (A : Space ℓ𝓤 ℓ𝓟 ℓ𝓞)
    → (X : 𝓟 {ℓ' = ℓ0} (A .Space.𝓤))
    → Space ℓ𝓤 ℓ𝓟 (ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞)
  Restriction A X = FreeSpace 𝓤' 𝓞Restr
    module _ where
    open Space A
    private
      𝓤' : Set ℓ𝓤
      𝓤' = ΣP 𝓤 X

    data 𝓞Restr : 𝓟 𝓤' → Prop (ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞) where
      restrict : (Y : 𝓟 𝓤) → 𝓞 Y → 𝓞Restr (λ (x , _) → Y x)

  Inclusion
    : (A : Space ℓ𝓤 ℓ𝓟 ℓ𝓞)
    → (X : 𝓟 {ℓ' = ℓ0} (A .Space.𝓤))
    → Restriction A X ⇒ A
  Inclusion A X = fst , f𝓞
    where
    module A = Space A
    module B = Space (Restriction A X)
    
    f𝓞 : (Y : 𝓟 A.𝓤) → A.𝓞 Y
       → B.𝓞 (λ (x , _) → Y x)
    f𝓞 Y A𝓞Y =
      𝓞∈[𝓞] (λ (x , _) → Y x)
            (restrict Y A𝓞Y)

-- Pointed spaces
Space· : ∀ ℓ𝓤 ℓ𝓟 ℓ𝓞 → Set (lsuc (ℓ𝓤 ⊔ ℓ𝓟 ⊔ ℓ𝓞))
Space· ℓ𝓤 ℓ𝓟 ℓ𝓞 = Σ (Space ℓ𝓤 ℓ𝓟 ℓ𝓞) ⟨_⟩
