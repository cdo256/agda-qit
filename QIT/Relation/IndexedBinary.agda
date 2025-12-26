module QIT.Relation.IndexedBinary where

open import QIT.Prelude
open import QIT.Relation.Base 

module _ 
  {ℓI ℓA ℓR} {I : Set ℓI} (A : I → Set ℓA) (R : IndexedBinaryRel A ℓR)
  where

  private
    infix 4 _≈_
    _≈_ : ∀ {i j} → A i → A j → Prop ℓR
    _≈_ {i} {j} x y = R i j x y

  Reflexive : Prop (ℓI ⊔ ℓA ⊔ ℓR)
  Reflexive = ∀ {i} {x : A i} → x ≈ x

  Symmetric : Prop (ℓI ⊔ ℓA ⊔ ℓR)
  Symmetric = ∀ {i j} {x : A i} {y : A j} → x ≈ y → y ≈ x

  Transitive : Prop (ℓI ⊔ ℓA ⊔ ℓR)
  Transitive = ∀ {i j k} {x : A i} {y : A j} {z : A k} → x ≈ y → y ≈ z → x ≈ z

  record IsEquivalence : Prop (ℓI ⊔ ℓA ⊔ ℓR) where
    field
      refl  : Reflexive
      sym   : Symmetric
      trans : Transitive
