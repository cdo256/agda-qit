module QIT.Relation.Ordinal where

open import QIT.Prelude
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Set.Base

record IsOrdinalStr {ℓA ℓ<} (A : Set ℓA) (_<_ : A → A → Prop ℓ<) : Prop (ℓA ⊔ ℓ<) where
  field
    trans : Transitive _<_
    wf : WellFounded _<_
    ext : ∀ α β → (∀ γ → γ < α ⇔ γ < β) → α ≡ β
    total : ∀ α β → α < β ∨ α ≡ β ∨ β < α

record IsOrdinal {ℓA} ℓ< (A : Set ℓA) : Set (ℓA ⊔ lsuc ℓ<) where
  field
    _<_ : A → A → Prop ℓ< 
    isOrd : IsOrdinalStr A _<_

Ordinal : ∀ ℓA ℓ< → Set (lsuc ℓA ⊔ lsuc ℓ<)
Ordinal ℓA ℓ< = Σ (Set ℓA) (IsOrdinal ℓ<)
