open import QIT.Prelude
open import QIT.Prop

module QIT.Types
  ⦃ pathELim* : PathElim ⦄
  where

data Maybep {ℓ} (X : Prop ℓ) :  Prop ℓ where
  nothing : Maybep X
  just : X → Maybep X 

mapBox : {P : Prop ℓP} {Q : Prop ℓQ} → (P → Q) → Box P → Box Q
mapBox f (box x) = box (f x)

inj₁≢inj₂ : {A : Set ℓA} {B : Set ℓB} {x : A} {y : B} → inj₁ x ≢ inj₂ y
inj₁≢inj₂ ()
