open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)

module QIT.Examples.Plump.Algebra {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

record Algebra ℓX : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓX) where
  field
    Z : Set ℓX
    sup : ⟦ S ◁ P ⟧ Z → Z
    _<_ : Z → Z → Prop (ℓS ⊔ ℓP)
    _≤_ : Z → Z → Prop (ℓS ⊔ ℓP)

    sup≤ : {s : S} {f : P s → Z} {α : Z}
          → (∀ i → f i < α)
          → sup (s , f) ≤ α
    <sup : {s : S} {f : P s → Z}
          → (i : P s) → {α : Z}
          → α ≤ f i
          → α < sup (s , f)

    ≤≤ : {α β γ : Z} → β ≤ γ → α ≤ β → α ≤ γ
    ≤< : {α β γ : Z} → β ≤ γ → α < β → α < γ
    <≤ : {α β γ : Z} → β < γ → α ≤ β → α < γ
    << : {α β γ : Z} → β < γ → α < β → α < γ
    <→≤ : {α β : Z} → α < β → α ≤ β

    ≤refl : ∀ α → α ≤ α

    ≤antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β

    iswf< : WellFounded _<_

record Hom {ℓX ℓY} (X-alg : Algebra ℓX) (Y-alg : Algebra ℓY) :
       Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓX ⊔ lsuc ℓY) where
  module X = Algebra X-alg
  module Y = Algebra Y-alg
  field
    Zʰ : X.Z → Y.Z
    supʰ : ∀ {s : S} {f : P s → X.Z}
         → Zʰ (X.sup (s , f)) ≡ Y.sup (s , λ i → Zʰ (f i))
    <ʰ : ∀ {α β : X.Z} → α X.< β → Zʰ α Y.< Zʰ β
    ≤ʰ : ∀ {α β : X.Z} → α X.≤ β → Zʰ α Y.≤ Zʰ β

record _≈ʰ_ {ℓX ℓY} {X-alg : Algebra ℓX} {Y-alg : Algebra ℓY}
            (fʰ gʰ : Hom X-alg Y-alg) :
            Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓX ⊔ lsuc ℓY)
            where
  constructor mk≈h
  module X = Algebra X-alg
  module Y = Algebra Y-alg
  module f = Hom fʰ
  module g = Hom gʰ
  field
    ≈Zʰ : ∀ x → f.Zʰ x ≡ g.Zʰ x
