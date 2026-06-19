module QIT.Prelude.Universe where

open import Agda.Primitive renaming (lzero to ℓ0) public

record Lift {ℓA} ℓA' (A : Set ℓA) : Set (ℓA ⊔ ℓA') where
  constructor lift
  field lower : A

open Lift public

record LiftP {ℓA} ℓA' (A : Prop ℓA) : Prop (ℓA ⊔ ℓA') where
  constructor liftp
  field lowerp : A

open LiftP public
