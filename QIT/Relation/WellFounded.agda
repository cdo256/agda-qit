module QIT.Relation.WellFounded where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base

module _ {ℓA ℓR} {A : Set ℓA} (R : A → A → Set ℓR) where
  WfRec : (A → Set (ℓA ⊔ ℓR)) → (A → Set (ℓA ⊔ ℓR))
  WfRec P x = ∀ y → R y x → P y

  data Acc (x : A) : Set (ℓA ⊔ ℓR) where
    acc : (rs : WfRec Acc x) → Acc x

  WellFounded : Set _
  WellFounded = ∀ x → Acc x

  Wf-ind : ∀ {ℓP}
    → WellFounded
    → (P : A → Set ℓP)
    → (step : ∀ x → (∀ y → R y x → P y) → P x)
    → ∀ x → P x
  Wf-ind wf P step x = sub (wf x)
    where
      sub : ∀ {x} → Acc x → P x
      sub (acc rs) = step _ (λ y ryx → sub (rs y ryx))

module _ {ℓA ℓB ℓR} {A : Set ℓA} {B : Set ℓB}
  (R : A → A → Set ℓR) (f : B → A)
  (wfR : WellFounded R) where

  private
    S : B → B → Set ℓR
    S x y = R (f x) (f y)

  mutual
    wfProj : WellFounded S
    wfProj x = wfProj-lift (wfR (f x)) ≡.refl

    wfProj-lift : ∀ {a} → Acc R a
                → ∀ {x} → f x ≡ a → Acc S x
    wfProj-lift (acc rs) {x} ≡.refl =
      acc (λ y syx → wfProj-lift (rs (f y) syx) ≡.refl)
