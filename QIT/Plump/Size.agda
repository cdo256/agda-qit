open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary using (WellFounded; WeakPreorder)
open import QIT.Relation.Subset
import QIT.Plump.Algebra

module QIT.Plump.Size where

record SizeStr {ℓZ} (Z : Set ℓZ)
  : Set (lsuc ℓZ) where
  infix  4 _<_
  infixr 6 _∨ᶻ_
  field
    _<_ : Z → Z → Prop ℓZ
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
  <wp : WeakPreorder Z _
  <wp = _<_ , record { trans = λ p q → << q p }
  ↓_ : Z → Set ℓZ
  ↓ α = ΣP Z (_< α)

plumpSizeStr
  : ⦃ pathElim* : PathElim ⦄
  → ∀ {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  → (Zᴬ : QIT.Plump.Algebra.PlumpAlgebra S P)
  → SizeStr (QIT.Plump.Algebra.PlumpAlgebra.Z Zᴬ)
plumpSizeStr Zᴬ = record
  { _<_ = Z._<_
  ; << = Z.<<
  ; iswf< = Z.iswf<
  ; ⊥ᶻ = Z.⊥ᶻ
  ; _∨ᶻ_ = Z._∨ᶻ_
  ; ∨ᶻ-l = Z.∨ᶻ-l<
  ; ∨ᶻ-r = Z.∨ᶻ-r< }
  where module Z = QIT.Plump.Algebra.PlumpAlgebra Zᴬ

module SizedTypes {ℓZ} {Z : Set ℓZ} (sz : SizeStr Z) where
  open SizeStr sz
  infix 4 _<ᵇ_

  _<ᵇ_ : Z → Z → Prop ℓZ
  _<ᵇ_ = _<_

  <ᵇ<ᵇ : ∀ {α β γ} → β <ᵇ γ → α <ᵇ β → α <ᵇ γ
  <ᵇ<ᵇ = <<

  Πᵇ : ∀ α {ℓA}
    → (A : ∀ β {_ : β < α} → Set ℓA)
    → Set (ℓZ ⊔ ℓA)
  Πᵇ α {ℓA} A = ∀ β {β<α} → A β {β<α}

  ∀ᵇ : ∀ α {ℓA}
    → (A : ∀ β {_ : β < α} → Prop ℓA)
    → Prop (ℓZ ⊔ ℓA)
  ∀ᵇ α A = ∀ β {β<α} → A β {β<α}

  record Σᵇ (α : Z) {ℓA} (A : ∀ β {_ : β < α} → Set ℓA)
    : Set (ℓA ⊔ ℓZ) where
    constructor pairᵇ
    field
      fst : Z
      {fst<} : fst < α
      snd : A fst {fst<}
  open Σᵇ public

  data ∃ᵇ (α : Z) {ℓA} (A : ∀ β {_ : β < α} → Prop ℓA)
    : Prop (ℓA ⊔ ℓZ) where
    ∃ᵇi : ∀ β {β<α} → A β {β<α} → ∃ᵇ α A
