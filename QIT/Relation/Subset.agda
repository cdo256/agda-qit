open import QIT.Prelude

module QIT.Relation.Subset ⦃ pathElim* : PathElim ⦄ where

open import QIT.Prelude
open import QIT.Prelude.Types using (ΣP; _,_; fst; snd; ⟨_⟩ᴾ) public
open import QIT.Identity using (ΣP≡; ΣP≡'; substΣP) public
open import QIT.Prop

Singleton : ∀ {ℓA} {A : Set ℓA} (a : A) → Set ℓA
Singleton {A = A} a = ΣP A (_≡ a)

inspect : ∀ {ℓA} {A : Set ℓA} (x : A) → Singleton x
inspect x = x , ≡.refl

𝓟 : ∀ {ℓ𝓤} ℓ𝓟 → (𝓤 : Set ℓ𝓤) → Set (ℓ𝓤 ⊔ lsuc ℓ𝓟)
𝓟 ℓ𝓟  𝓤 = 𝓤 → Prop ℓ𝓟

module Subset {ℓ𝓤} ℓ𝓟 (𝓤 : Set ℓ𝓤) where
  𝓟𝓤 = 𝓟 ℓ𝓟 𝓤
  open import QIT.List

  infix 30 _∈_
  infix 40 _∪_ _∩_
  _∈_ : (x : 𝓤) (X : 𝓟𝓤) → Prop ℓ𝓟
  x ∈ X = X x

  ∅ : 𝓟𝓤
  ∅ _ = ⊥*

  𝓤̇ : 𝓟𝓤
  𝓤̇ _ = ⊤*

  [_]ᴾ : List 𝓤 → 𝓟 (ℓ𝓤 ⊔ ℓ𝓟) 𝓤
  [ [] ]ᴾ _ = ⊥*
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
