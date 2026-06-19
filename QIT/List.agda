open import QIT.Prelude

module QIT.List where

data List {ℓA} (A : Set ℓA) : Set ℓA where
  [] : List A
  _∷_ : A → List A → List A
