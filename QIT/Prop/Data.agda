open import QIT.Prelude

module QIT.Prop.Data ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop.Base
open import QIT.Prelude.Logic

data Maybep {ℓ} (X : Prop ℓ) :  Prop ℓ where
  nothing : Maybep X
  just : X → Maybep X 

mapBox : ∀ {ℓP ℓQ} {P : Prop ℓP} {Q : Prop ℓQ} → (P → Q) → Box P → Box Q
mapBox f (box x) = box (f x)
