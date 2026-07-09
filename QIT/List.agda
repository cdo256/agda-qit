open import QIT.Prelude

module QIT.List where

infixl 6 _∷_ _++_
data List (A : Set ℓA) : Set ℓA where
  [] : List A
  _∷_ : A → List A → List A

_++_ : {A : Set ℓA} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
