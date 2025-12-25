{-# OPTIONS --type-in-type #-}

module QIT.Setoid.Functor where

open import QIT.Prelude
open import QIT.Setoid.Base
open import QIT.Setoid.Hom
open import Data.Product

private
  variable
    ℓ ℓ' : Level

record Functor ℓ ℓ' : Set where
  field
    F-ob : ∀ (S : Setoid ℓ ℓ') → Setoid ℓ ℓ'
    F-mor : ∀ {S T : Setoid ℓ ℓ'} → Hom S T → Hom (F-ob S) (F-ob T)
    F-id : ∀ {S : Setoid ℓ ℓ'} → F-mor idHom ≈h idHom {S = F-ob S}
    F-comp : ∀ {S T U : Setoid ℓ ℓ'} → (f : Hom S T) → (g : Hom T U)
           → F-mor (g ∘ f) ≈h (F-mor g ∘ F-mor f)
    F-resp : ∀ {S T} {f g : Hom S T} → f ≈h g → F-mor f ≈h F-mor g
