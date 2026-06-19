open import QIT.Prelude

module QIT.HLevel where

open import QIT.Prop
open import QIT.Function.Base

hProp→Prop : ∀ {ℓA} → hProp ℓA → Prop ℓA
hProp→Prop (A , _) = ∥ A ∥

Prop→hProp : ∀ {ℓA} → Prop ℓA → hProp ℓA
Prop→hProp A = Box A , ≡.isPropBox

mkIsContr
  : ∀ {ℓA} → (A : Set ℓA)
  → ∥ A ∥ → isProp A → isContr A
mkIsContr A ∣ x ∣ isPropA = ∣ x , isPropA x ∣

Σ≡Prop
  : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
  → ((x : A) → isProp (B x)) → {u v : Σ A B}
  → (p : u .proj₁ ≡ v .proj₁) → u ≡ v
Σ≡Prop pB {x , u} {x , v} ≡.refl =
  ≡.cong (x ,_) (pB x u v)

isSetSet : ∀ {ℓA} {A : Set ℓA} {x y : A} (p q : x ≡ y) → p ≡ᵖ q
isSetSet ≡.refl ≡.refl = ≡.refl

module _ (a!c : A!C) where
  a!c-Prop : ∀ {ℓX} (X : Set ℓX)
            → isProp X → (Box ∥ X ∥) ↔ X
  a!c-Prop X isPropX = record
    { to = λ (box x) → a!c X (mkIsContr X x isPropX)
    ; from = λ z → box ∣ z ∣
    ; rinv = λ _ → ≡.isPropBox _ _
    ; linv = λ _ → isPropX _ _ }

  Prop≅hProp-sect
    : ∀ {ℓA} → (A : hProp ℓA)
    → Prop→hProp (hProp→Prop A) .fst ↔ A .fst
  Prop≅hProp-sect (A , isPropA) = a!c-Prop A isPropA
