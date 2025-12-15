module WellFounded where

open import Level using (Level; _⊔_) renaming (suc to lsuc)

module _ {ℓA ℓ<} {A : Set ℓA} (_<_ : A → A → Prop ℓ<) where
    WfRec : (A → Prop (ℓA ⊔ ℓ<)) → (A → Prop (ℓA ⊔ ℓ<))
    WfRec P x = ∀ y → y < x → P y

    data Acc (x : A) : Prop (ℓA ⊔ ℓ<) where
      acc : (rs : WfRec Acc x) → Acc x

    WellFounded : Prop _
    WellFounded = ∀ x → Acc x
