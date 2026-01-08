module QIT.Setoid where

module ≈ where
  open import QIT.Setoid.Base public
  open import QIT.Setoid.Hom public
  open import QIT.Setoid.Iso public
  open import QIT.Setoid.Functor public
  open import QIT.Setoid.Algebra public

open ≈ using (≡setoid; Setoid; ⟨_⟩; _≈h_; _[_≈_]; _≅_; ≡→≈) public
