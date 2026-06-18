module QIT.Relation.Base where

open import QIT.Prelude

BinaryRel : ∀ {ℓA} (A : Set ℓA) ℓR → Set (ℓA ⊔ lsuc ℓR)
BinaryRel A ℓR = A → A → Prop ℓR

BinaryRelˢ : ∀ {ℓA} (A : Set ℓA) ℓR → Set (ℓA ⊔ lsuc ℓR)
BinaryRelˢ A ℓR = A → A → Set ℓR

IndexedBinaryRel : ∀ {ℓI ℓA} {I : Set ℓI} (A : I → Set ℓA) ℓR → Set (ℓI ⊔ ℓA ⊔ lsuc ℓR)
IndexedBinaryRel A ℓR = ∀ i j → A i → A j → Prop ℓR

IndexedBinaryRelˢ : ∀ {ℓI ℓA} {I : Set ℓI} (A : I → Set ℓA) ℓR → Set (ℓI ⊔ ℓA ⊔ lsuc ℓR)
IndexedBinaryRelˢ A ℓR = ∀ i j → A i → A j → Set ℓR
