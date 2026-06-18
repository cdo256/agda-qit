module QIT.Relation.Binary where

open import QIT.Prelude
open import QIT.Prop
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

module _ {ℓA ℓR} {A : Set ℓA} (R : BinaryRelˢ A ℓR) where
  Reflexiveˢ : Set (ℓA ⊔ ℓR)
  Reflexiveˢ = ∀ {x} → R x x

  Symmetricˢ : Set (ℓA ⊔ ℓR)
  Symmetricˢ = ∀ {x y} → R x y → R y x

  Transitiveˢ : Set (ℓA ⊔ ℓR)
  Transitiveˢ = ∀ {x y z} → R x y → R y z → R x z

  WfRecˢ : (A → Set (ℓA ⊔ ℓR)) → (A → Set (ℓA ⊔ ℓR))
  WfRecˢ P x = ∀ y → R y x → P y

  data Accˢ (x : A) : Set (ℓA ⊔ ℓR) where
    acc : (rs : WfRecˢ Accˢ x) → Accˢ x

  WellFoundedˢ : Set _
  WellFoundedˢ = ∀ x → Accˢ x

  record IsEquivalenceˢ : Set (ℓR ⊔ ℓA) where
    field
      refl  : Reflexiveˢ
      sym   : Symmetricˢ
      trans : Transitiveˢ

  record IsPreorderˢ : Set (ℓR ⊔ ℓA) where
    field
      refl  : Reflexiveˢ
      trans : Transitiveˢ

Preorder : ∀ {ℓA} (S : Set ℓA) → ∀ ℓR → Set (ℓA ⊔ lsuc ℓR)
Preorder S ℓR = Σ (BinaryRel S ℓR) IsPreorder

Preorderˢ : ∀ {ℓA} (S : Set ℓA) → ∀ ℓR → Set (ℓA ⊔ lsuc ℓR)
Preorderˢ S ℓR = Σ (BinaryRelˢ S ℓR) IsPreorderˢ

module _ {ℓA} (A : Set ℓA) where
  private
    R : BinaryRel A ℓA
    R = _≡_

  isEquiv-≡ : IsEquivalence (_≡_ {A = A})
  isEquiv-≡ = record { refl = ≡.refl ; sym = sym ; trans = trans }
    where
    sym : Symmetric R
    sym ≡.refl = ≡.refl
    trans : Transitive R
    trans ≡.refl ≡.refl = ≡.refl

module _ {ℓA} (A : Set ℓA) where
  private
    R : BinaryRelˢ A ℓA
    R = _≡ˢ_

  isEquiv-≡ˢ : IsEquivalenceˢ (_≡ˢ_ {A = A})
  isEquiv-≡ˢ = record { refl = reflˢ ; sym = sym ; trans = trans }
    where
    sym : Symmetricˢ R
    sym reflˢ = reflˢ
    trans : Transitiveˢ R
    trans reflˢ reflˢ = reflˢ

module _ {ℓA ℓB ℓR} {A : Set ℓA} {B : Set ℓB}
  (R : BinaryRel A ℓR) (f : B → A)
  (wfR : WellFounded R) where

  private
    S : BinaryRel B ℓR
    S x y = R (f x) (f y)

  mutual
    wfProj : WellFounded S
    wfProj x = wfProj-lift (wfR (f x)) ≡.refl

    wfProj-lift : ∀ {a} → Acc R a
                → ∀ {x} → f x ≡ a → Acc S x
    wfProj-lift (acc rs) {x} ≡.refl =
      acc (λ y syx → wfProj-lift (rs (f y) syx) ≡.refl)

module _ {ℓA ℓB ℓR} {A : Set ℓA} {B : Set ℓB}
  (R : BinaryRelˢ A ℓR) (f : B → A)
  (wfR : WellFoundedˢ R) where

  private
    S : BinaryRelˢ B ℓR
    S x y = R (f x) (f y)

  mutual
    wfProjˢ : WellFoundedˢ S
    wfProjˢ x = wfProjˢ-lift (wfR (f x)) reflˢ

    wfProjˢ-lift : ∀ {a} → Accˢ R a
                → ∀ {x} → f x ≡ˢ a → Accˢ S x
    wfProjˢ-lift (acc rs) {x} reflˢ =
      acc (λ y syx → wfProjˢ-lift (rs (f y) syx) reflˢ)
