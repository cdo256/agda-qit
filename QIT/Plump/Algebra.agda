open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.Algebra {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

record Algebra ℓA : Set (lsuc ℓA ⊔ lsuc ℓS ⊔ lsuc ℓP) where
  field
    Z : Set ℓA
    sup : Σ S (λ s → P s → Z) → Z
    _<_ : Z → Z → Prop ℓA
    _≤_ : Z → Z → Prop ℓA

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

    iswf< : WellFounded _<_

record Displayed ℓA (Zᴬ : Algebra ℓA) 
  : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra Zᴬ
  field
    Zᴰ : Z → Set ℓA
    supᴰ : ∀ s → {ξ : P s → Z} (f : ∀ i → Zᴰ (ξ i)) → Zᴰ (sup (s , ξ))
    _⊢_<ᴰ_ : ∀ {α β} → α < β → Zᴰ α → Zᴰ β → Prop ℓA
    _⊢_≤ᴰ_ : ∀ {α β} → α ≤ β → Zᴰ α → Zᴰ β → Prop ℓA

    sup≤ᴰ : {s : S} {ξ : P s → Z} {α : Z}
          → {f : ∀ i → Zᴰ (ξ i)}
          → {x : Zᴰ α}
          → (p : ∀ i → ξ i < α)
          → (∀ i → p i ⊢ f i <ᴰ x)
          → sup≤ p ⊢ supᴰ s f ≤ᴰ x
    <supᴰ : {s : S} {ξ : P s → Z} {α : Z}
          → {f : ∀ i → Zᴰ (ξ i)} {x : Zᴰ α}
          → (i : P s)
          → (p : α ≤ ξ i)
          → p ⊢ x ≤ᴰ f i
          → <sup i p ⊢ x <ᴰ supᴰ s f

    ≤≤ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β ≤ γ} → {p : α ≤ β}
        → q ⊢ y ≤ᴰ z → p ⊢ x ≤ᴰ y → ≤≤ q p ⊢ x ≤ᴰ z
    <≤ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β < γ} → {p : α ≤ β}
        → q ⊢ y <ᴰ z → p ⊢ x ≤ᴰ y → <≤ q p ⊢ x <ᴰ z
    ≤<ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β ≤ γ} → {p : α < β}
        → q ⊢ y ≤ᴰ z → p ⊢ x <ᴰ y → ≤< q p ⊢ x <ᴰ z
    <<ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β < γ} → {p : α < β}
        → q ⊢ y <ᴰ z → p ⊢ x <ᴰ y → << q p ⊢ x <ᴰ z
    <→≤ᴰ : {α β : Z} {p : α < β} {x : Zᴰ α} {y : Zᴰ β}
         → p ⊢ x <ᴰ y → <→≤ p ⊢ x ≤ᴰ y

    ≤reflᴰ : ∀ {α} {x : Zᴰ α} → ≤refl α ⊢ x ≤ᴰ x

    --TODO: Do I need this in the displayed models?
    -- iswf< : WellFounded _<ᴰ_

record Elim {ℓA} {ZA : Algebra ℓA}
  (ZD : Displayed ℓA ZA)
  : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra ZA
  open Displayed ZD
  field
    Zᴱ : ∀ α → Zᴰ α
    supᴱ : ∀ s (ξ : P s → Z)
         → supᴰ s (λ i → Zᴱ (ξ i)) ≡ Zᴱ (sup (s , ξ))
    <ᴱ : ∀ {α β} → (p : α < β) → p ⊢ Zᴱ α <ᴰ Zᴱ β
    ≤ᴱ : ∀ {α β} → (p : α ≤ β) → p ⊢ Zᴱ α ≤ᴰ Zᴱ β

record _≈ᴱ_ {ℓA} {ZA : Algebra ℓA} {ZD : Displayed ℓA ZA}
              (e₁ e₂ : Elim ZD) : Prop (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  module e₁ = Elim e₁
  module e₂ = Elim e₂
  field
    Zᴱ : ∀ α → e₁.Zᴱ α ≡ e₂.Zᴱ α

record IsExtensional {ℓA} (ZA : Algebra ℓA) : Prop ℓA where
  open Algebra ZA
  field
    antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β

record IsExtensionalᴰ {ℓA} {ZA : Algebra ℓA} (ZD : Displayed ℓA ZA) : Prop ℓA where
  open Algebra ZA
  open Displayed ZD
  field
    isExtZA : IsExtensional ZA

  open IsExtensional isExtZA public
  field
    antisymᴰ : ∀ {α β} → (p : α ≤ β) → (q : β ≤ α)
            → {x : Zᴰ α} {y : Zᴰ β}
            → p ⊢ x ≤ᴰ y → q ⊢ y ≤ᴰ x
            → subst Zᴰ (antisym p q) x ≡ y

record IsInitial {ℓA} (ZA : Algebra ℓA) : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra ZA
  field
    elim : (ZD : Displayed ℓA ZA) → Elim ZD
    elim-unique : ∀ ZD → (e : Elim ZD) → elim ZD ≈ᴱ e

record IsInitialExt {ℓA} (ZA : Algebra ℓA) : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra ZA
  field
    ext : IsExtensional ZA
    elim : (ZD : Displayed ℓA ZA)
         → IsExtensionalᴰ ZD
         → Elim ZD
    elim-unique : ∀ ZD isExtZD e → elim ZD isExtZD ≈ᴱ e
