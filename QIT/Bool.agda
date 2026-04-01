module QIT.Bool where

open import QIT.Prelude
open import QIT.Prop
open import Data.Bool.Base
import Data.Bool.Properties as 𝔹

not-involutive : (b : Bool) → not (not b) ≡ b
not-involutive false = ≡.refl
not-involutive true = ≡.refl
