module QIT.Bool where

open import QIT.Prelude
open import QIT.Prop
open import Data.Bool

_?ᴮ : ∀ b → Dec (b ≡ true)
false ?ᴮ = no (λ ())
true ?ᴮ = yes ≡.refl
