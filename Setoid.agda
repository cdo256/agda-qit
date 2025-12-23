module Setoid where

module ≈ where
  open import Setoid.Base public
  open import Setoid.Hom public
  open import Setoid.Iso public
  open import Setoid.Functor public

open ≈ using (≡setoid; Setoid; ⟨_⟩; _≈h_; _[_≈_]; _≅_; ≡→≈) public
