open import QIT.Prelude

module QIT.Maybe ⦃ a!c* : A!C ⦄ where

data Maybe {ℓA} (A : Set ℓA) : Set ℓA where 
  nothing : Maybe A
  just : A → Maybe A

map : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → (A → B) → Maybe A → Maybe B
map f nothing = nothing
map f (just x) = just (f x)
