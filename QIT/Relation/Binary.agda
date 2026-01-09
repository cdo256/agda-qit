module QIT.Relation.Binary where

open import QIT.Prelude
open import QIT.Relation.Base

module _ {ℓA ℓR} {A : Set ℓA} (R : BinaryRel A ℓR) where
  Reflexive : Prop (ℓA ⊔ ℓR)
  Reflexive = ∀ {x} → R x x

  Symmetric : Prop (ℓA ⊔ ℓR)
  Symmetric = ∀ {x y} → R x y → R y x

  Transitive : Prop (ℓA ⊔ ℓR)
  Transitive = ∀ {x y z} → R x y → R y z → R x z

  WfRec : (A → Prop (ℓA ⊔ ℓR)) → (A → Prop (ℓA ⊔ ℓR))
  WfRec P x = ∀ y → R y x → P y

  data Acc (x : A) : Prop (ℓA ⊔ ℓR) where
    acc : (rs : WfRec Acc x) → Acc x

  WellFounded : Prop _
  WellFounded = ∀ x → Acc x

  record IsEquivalence : Prop (ℓR ⊔ ℓA) where
    field
      refl  : Reflexive
      sym   : Symmetric
      trans : Transitive

  record IsPreorder : Set (ℓR ⊔ ℓA) where
    field
      refl  : Reflexive
      trans : Transitive

Preorder : ∀ {ℓA} (S : Set ℓA) → ∀ ℓR → Set (ℓA ⊔ lsuc ℓR)
Preorder S ℓR = Σ (BinaryRel S ℓR) IsPreorder

module _ {ℓA} (A : Set ℓA) where
  private
    R : BinaryRel A ℓA
    R = _≡p_

  isEquiv-≡p : IsEquivalence (_≡p_ {A = A})
  isEquiv-≡p = record { refl = ∣ refl ∣ ; sym = sym ; trans = trans }
    where
    open _≡_
    sym : Symmetric R
    sym ∣ refl ∣ = ∣ refl ∣
    trans : Transitive R
    trans ∣ refl ∣ ∣ refl ∣ = ∣ refl ∣
