module QIT.Examples.HoleList where

open import QIT.Prelude

infixr 30 _∷_
infixr 30 ●∷_

data HoleList (A : Set) : Set where
  [] : HoleList A
  ●∷_ : HoleList A → HoleList A
  _∷_ : A → HoleList A → HoleList A

module _ {A : Set} where
  data _≈_ : HoleList A → HoleList A → Prop where
    ≈refl : ∀ xs → xs ≈ xs
    ≈swap : ∀ x y xs → x ∷ y ∷ xs ≈ y ∷ x ∷ xs
    ≈hole : ∀ x y xs → x ∷ xs ≈ y ∷ xs → x ∷ ●∷ xs ≈ y ∷ ●∷ xs
    ≈cong₁ : ∀ x y z xs → x ∷ xs ≈ y ∷ xs → x ∷ z ∷ xs ≈ y ∷ z ∷ xs
    ≈cong₂ : ∀ x y z xs → x ∷ xs ≈ y ∷ xs → z ∷ x ∷ xs ≈ z ∷ y ∷ xs

  data _≈'_ : HoleList A → HoleList A → Prop where
    ≈nil : [] ≈' []
    ≈swap : ∀ x y xs → x ∷ y ∷ xs ≈' y ∷ x ∷ xs
    ≈hole : ∀ x y xs → x ∷ xs ≈' y ∷ xs → x ∷ ●∷ xs ≈' y ∷ ●∷ xs
    ≈cong₁ : ∀ x y z xs → x ∷ xs ≈' y ∷ xs → x ∷ z ∷ xs ≈' y ∷ z ∷ xs
    ≈cong₂ : ∀ x y z xs → x ∷ xs ≈' y ∷ xs → z ∷ x ∷ xs ≈' z ∷ y ∷ xs
