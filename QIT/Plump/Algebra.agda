open import QIT.Prelude
open import QIT.Prop hiding (⊥; _∨_)
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.Algebra
  ⦃ pathElim* : PathElim ⦄       
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) ℓZ ℓ< ℓ≤
  where

record PlumpAlgebra
  : Set (lsuc ℓZ ⊔ lsuc ℓ< ⊔ lsuc ℓ≤ ⊔ lsuc ℓS ⊔ lsuc ℓP) where

  infix 4 _≤_ _<_
  infixl 10 _∨ᶻ_

  private
    T = W.W S P

  field
    Z : Set ℓZ
    sup : Σ S (λ s → P s → Z) → Z
    _<_ : Z → Z → Prop ℓ<
    _≤_ : Z → Z → Prop ℓ≤

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

    _∨ᶻ_ : Z → Z → Z
    ∨ᶻ-l< : ∀ {α β} → α < (α ∨ᶻ β)
    ∨ᶻ-r< : ∀ {α β} → β < (α ∨ᶻ β)
    ∨ᶻ-flip : ∀ {α β} → (β ∨ᶻ α) ≤ (α ∨ᶻ β)

    ⊥ᶻ : Z
    ⊥ᶻ≤ : ∀ {α} → ⊥ᶻ ≤ α

    -- iswf< : WellFounded _<_

  record IsExtensional : Prop (ℓZ ⊔ ℓ≤) where
    field
      antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β
