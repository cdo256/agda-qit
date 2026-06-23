module QIT.Prelude.HLevel where

open import QIT.Prelude.Universe
open import QIT.Prelude.Types
open import QIT.Prelude.Truncation
open import QIT.Prelude.Identity
open import QIT.Prelude.Logic

isProp : Set ℓA → Prop ℓA
isProp A = ∀ (x y : A) → x ≡ y

hProp : ∀ ℓA → Set (lsuc ℓA)
hProp ℓA = ΣP (Set ℓA) isProp

isContr : Set ℓA → Prop ℓA
isContr A = ∃ λ (x : A) → ∀ y → x ≡ y
