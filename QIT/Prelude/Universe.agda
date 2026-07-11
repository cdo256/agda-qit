module QIT.Prelude.Universe where

open import Agda.Primitive renaming (lzero to ℓ0) public

ℓ1 = lsuc ℓ0
ℓ2 = lsuc ℓ1

variable
  ℓA ℓB ℓC ℓD ℓE ℓF ℓI ℓP ℓQ ℓR ℓS ℓX ℓY ℓZ : Level

record Lift ℓA' (A : Set ℓA) : Set (ℓA ⊔ ℓA') where
  constructor lift
  field lower : A

open Lift public

record LiftP ℓA' (A : Prop ℓA) : Prop (ℓA ⊔ ℓA') where
  constructor liftp
  field lowerp : A

open LiftP public


