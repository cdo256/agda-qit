module QIT.Topology.Subset where

open import QIT.Prelude
open import QIT.Prop
open import Data.List
open import QIT.Relation.Subset

𝓟 : ∀ {ℓ𝓤} ℓ𝓟 → (𝓤 : Set ℓ𝓤) → Set (ℓ𝓤 ⊔ lsuc ℓ𝓟)
𝓟 ℓ𝓟  𝓤 = 𝓤 → Prop ℓ𝓟

module _ {ℓ𝓤 ℓ𝓟} {𝓤 : Set ℓ𝓤} where
  𝓟𝓤 = 𝓟 ℓ𝓟 𝓤

  infix 30 _∈_
  infix 40 _∪_ _∩_
  _∈_ : (x : 𝓤) (X : 𝓟𝓤) → Prop ℓ𝓟
  x ∈ X = X x

  ∅ : 𝓟𝓤
  ∅ _ = ⊥p*

  𝓤̇ : 𝓟𝓤
  𝓤̇ _ = ⊤p*

  [_]ᴾ : List 𝓤 → 𝓟 (ℓ𝓤 ⊔ ℓ𝓟) 𝓤
  [ [] ]ᴾ _ = ⊥p*
  [ x ∷ xs ]ᴾ y = (x ≡ y) ∨ ([ xs ]ᴾ y)

  _∪_ : 𝓟𝓤 → 𝓟𝓤 → 𝓟𝓤
  (X ∪ Y) x = x ∈ X ∨ x ∈ Y

  _∩_ : 𝓟𝓤 → 𝓟𝓤 → 𝓟𝓤
  (X ∩ Y) x = x ∈ X ∧ x ∈ Y

  ⋃ : ∀ {ℓI} (I : Set ℓI) → (I → 𝓟𝓤) → 𝓟 (ℓ𝓟 ⊔ ℓI) 𝓤
  ⋃ I X x = ∃ λ i → x ∈ X i

  ⋂ : ∀ {ℓI} (I : Set ℓI) → (I → 𝓟𝓤) → 𝓟 (ℓ𝓟 ⊔ ℓI) 𝓤
  ⋂ I X x = ∀ i → x ∈ X i

  record _↔ₛ_ (X Y : 𝓟𝓤) : Set (ℓ𝓟 ⊔ ℓ𝓤) where
    field
      to   : ∀ x → X x → Y x
      from : ∀ x → Y x → X x

infix 40 _×ˢ_ _+ˢ_

_×ˢ_ : ∀ {ℓ𝓤 ℓ𝓥 ℓ𝓟} {𝓤 : Set ℓ𝓤} {𝓥 : Set ℓ𝓥}
     → 𝓟 ℓ𝓟 𝓤 → 𝓟 ℓ𝓟 𝓥 → 𝓟 _ (𝓤 × 𝓥)
(X ×ˢ Y) (x , y) = x ∈ X ∧ y ∈ Y

⨅ˢ : ∀ {ℓJ ℓ𝓤 ℓ𝓟} (J : Set ℓJ) {𝓤 : J → Set ℓ𝓤}
     →  (Aᴶ : ∀ j → 𝓟 ℓ𝓟 (𝓤 j)) → 𝓟 (ℓJ ⊔ ℓ𝓟) (∀ j → 𝓤 j)
⨅ˢ J Aᴶ X = ∀ j → Aᴶ j (X j)


_+ˢ_ : ∀ {ℓ𝓤 ℓ𝓥 ℓ𝓟} {𝓤 : Set ℓ𝓤} {𝓥 : Set ℓ𝓥}
     → 𝓟 ℓ𝓟 𝓤 → 𝓟 ℓ𝓟 𝓥 → 𝓟 _ (𝓤 ⊎ 𝓥)
(X +ˢ Y) (inj₁ x) = x ∈ X
(X +ˢ Y) (inj₂ y) = y ∈ Y


⨆ˢ : ∀ {ℓJ ℓ𝓤 ℓ𝓟} (J : Set ℓJ) {𝓤 : J → Set ℓ𝓤}
     →  (Aᴶ : ∀ j → 𝓟 ℓ𝓟 (𝓤 j)) → 𝓟 _ (Σ J 𝓤)
⨆ˢ J Aᴶ (j , x) = x ∈ Aᴶ j
