open import QIT.Functor.Base
open import QIT.Category.Set

module QIT.Algebra {ℓC} (F : Functor (SetCat ℓC) (SetCat ℓC)) where

module Alg where
  open import QIT.Algebra.Base F public

open Alg public using (Algebra)
