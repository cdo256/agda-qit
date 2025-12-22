module Subset where

open import Prelude
open import Data.Product

record ΣP {a b} (A : Set a) (B : A → Prop b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open ΣP public

infixr 4 _,_

