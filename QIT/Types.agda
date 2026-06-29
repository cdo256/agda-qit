open import QIT.Prelude

module QIT.Types where

data Maybep {ℓ} (X : Prop ℓ) :  Prop ℓ where
  nothing : Maybep X
  just : X → Maybep X 

mapBox : ∀ {ℓP ℓQ} {P : Prop ℓP} {Q : Prop ℓQ} → (P → Q) → Box P → Box Q
mapBox f (box x) = box (f x)
