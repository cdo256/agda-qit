open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)

module QIT.Examples.Plump.DisplayedAlgebra
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  where

open import QIT.Examples.Plump.Algebra S P

record Displayed
  {ℓX} (X-alg : Algebra ℓX) (ℓD : Level)
  : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓX ⊔ lsuc ℓD) where

  module X = Algebra X-alg

  field
    Zᴰ : X.Z → Set ℓD

    supᴰ : {s : S} {f : P s → X.Z}
         → (fᴰ : ∀ i → Zᴰ (f i))
         → Zᴰ (X.sup (s , f))

    <ᴰ : {α β : X.Z}
       → Zᴰ α → Zᴰ β → α X.< β → Set ℓD

    ≤ᴰ : {α β : X.Z}
       → Zᴰ α → Zᴰ β → α X.≤ β → Set ℓD

    sup≤ᴰ
      : {s : S} {f : P s → X.Z} {α : X.Z}
      → (fᴰ : ∀ i → Zᴰ (f i))
      → (αᴰ : Zᴰ α)
      → (r : ∀ i → f i X.< α)
      → (rᴰ : ∀ i → <ᴰ (fᴰ i) αᴰ (r i))
      → ≤ᴰ (supᴰ fᴰ) αᴰ (X.sup≤ r)

    <supᴰ
      : {s : S} {f : P s → X.Z}
      → (fᴰ : ∀ i → Zᴰ (f i))
      → (i : P s) → {α : X.Z}
      → (αᴰ : Zᴰ α)
      → (r : α X.≤ f i)
      → (rᴰ : ≤ᴰ αᴰ (fᴰ i) r)
      → <ᴰ αᴰ (supᴰ fᴰ) (X.<sup i r)

    ≤≤ᴰ
      : {α β γ : X.Z}
      → {αᴰ : Zᴰ α} {βᴰ : Zᴰ β} {γᴰ : Zᴰ γ}
      → (p : β X.≤ γ) → (q : α X.≤ β)
      → ≤ᴰ βᴰ γᴰ p
      → ≤ᴰ αᴰ βᴰ q
      → ≤ᴰ αᴰ γᴰ (X.≤≤ p q)

    ≤<ᴰ
      : {α β γ : X.Z}
      → {αᴰ : Zᴰ α} {βᴰ : Zᴰ β} {γᴰ : Zᴰ γ}
      → (p : β X.≤ γ) → (q : α X.< β)
      → ≤ᴰ βᴰ γᴰ p
      → <ᴰ αᴰ βᴰ q
      → <ᴰ αᴰ γᴰ (X.≤< p q)

    <≤ᴰ
      : {α β γ : X.Z}
      → {αᴰ : Zᴰ α} {βᴰ : Zᴰ β} {γᴰ : Zᴰ γ}
      → (p : β X.< γ) → (q : α X.≤ β)
      → <ᴰ βᴰ γᴰ p
      → ≤ᴰ αᴰ βᴰ q
      → <ᴰ αᴰ γᴰ (X.<≤ p q)

    <<ᴰ
      : {α β γ : X.Z}
      → {αᴰ : Zᴰ α} {βᴰ : Zᴰ β} {γᴰ : Zᴰ γ}
      → (p : β X.< γ) → (q : α X.< β)
      → <ᴰ βᴰ γᴰ p
      → <ᴰ αᴰ βᴰ q
      → <ᴰ αᴰ γᴰ (X.<< p q)

    <→≤ᴰ
      : {α β : X.Z}
      → {αᴰ : Zᴰ α} {βᴰ : Zᴰ β}
      → (p : α X.< β)
      → <ᴰ αᴰ βᴰ p
      → ≤ᴰ αᴰ βᴰ (X.<→≤ p)

    ≤reflᴰ
      : {α : X.Z}
      → (αᴰ : Zᴰ α)
      → ≤ᴰ αᴰ αᴰ (X.≤refl α)

    ≤antisymᴰ
      : {α β : X.Z}
      → {αᴰ : Zᴰ α} {βᴰ : Zᴰ β}
      → (p : α X.≤ β) → (q : β X.≤ α)
      → ≤ᴰ αᴰ βᴰ p
      → ≤ᴰ βᴰ αᴰ q
      → subst Zᴰ (X.≤antisym p q) αᴰ ≡ βᴰ
