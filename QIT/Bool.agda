module QIT.Bool where

open import QIT.Prelude
open import QIT.Prop

not : Bool → Bool
not true = false
not false = true

not-involutive : (b : Bool) → not (not b) ≡ b
not-involutive false = ≡.refl
not-involutive true = ≡.refl
