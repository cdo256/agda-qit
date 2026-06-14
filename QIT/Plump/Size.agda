open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.Size {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

record SizeStr {ℓZ} (Z : Set ℓZ)
  : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓZ) where
  infix  4 _<_
  infixr 6 _∨ᶻ_
  field
    _<_ : Z → Z → Prop (ℓS ⊔ ℓP)
    << : {α β γ : Z} → β < γ → α < β → α < γ
    iswf< : WellFounded _<_
    ⊥ᶻ : Z
    _∨ᶻ_ : Z → Z → Z
    ∨ᶻ-l : ∀ {α β} → α < α ∨ᶻ β
    ∨ᶻ-r : ∀ {α β} → β < α ∨ᶻ β
  ↑ᶻ : Z → Z
  ↑ᶻ α = α ∨ᶻ α
  ↑ᶻ< : ∀ {α} → α < ↑ᶻ α
  ↑ᶻ< = ∨ᶻ-l
  ↓_ : Z → Set (ℓS ⊔ ℓP ⊔ ℓZ)
  ↓ α = ΣP Z (_< α)

module SizedTypes {ℓZ} {Z : Set ℓZ} (sz : SizeStr Z) where
  open SizeStr sz
  Πᵇ : ∀ α {ℓA}
    → (A : ∀ β {_ : β < α} → Set ℓA)
    → Set (ℓS ⊔ ℓP ⊔ ℓZ ⊔ ℓA)
  Πᵇ α {ℓA} A = ∀ β {β<α} → A β {β<α} 

  record Σᵇ (α : Z) {ℓA} (A : ∀ β {_ : β < α} → Set ℓA)
    : Set (ℓS ⊔ ℓP ⊔ ℓZ ⊔ ℓA) where
    field
      fst : Z
      {fst<} : fst < α
      snd : A fst {fst<}
  open Σᵇ public

