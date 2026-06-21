module Logic.Prelude.HLevel where

open import Logic.Prelude.Universe
open import Logic.Prelude.Types
open import Logic.Prelude.Truncation
open import Logic.Prelude.Identity
open import Logic.Prelude.Logic

const : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → A → B → A
const a _ = a

isProp : ∀ {ℓA} → Set ℓA → Prop ℓA
isProp A = ∀ (x y : A) → x ≡ y

hProp : ∀ ℓA → Set (lsuc ℓA)
hProp ℓA = ΣP (Set ℓA) isProp

isContr : ∀ {ℓA} → Set ℓA → Prop ℓA
isContr A = ∃ λ (x : A) → ∀ y → x ≡ y

