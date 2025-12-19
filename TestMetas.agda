{-# OPTIONS --type-in-type #-}
open import Prelude
open import Setoid
open import Equivalence
open import Data.Product

open import Data.Container hiding (refl; sym; trans)

module TestMetas (C : Container lzero lzero) where

private
  l0 = lzero

-- Import the problematic module
open import ContainerFunctor C

-- Test the specific area where metas occur
test-comp : {S T U : Setoid l0 l0} (f : ≈.Hom S T) (g : ≈.Hom T U) →
           ≈.Hom≈ (F̃-mor (g ≈.∘ f)) (F̃-mor g ≈.∘ F̃-mor f)
test-comp f g = F̃-comp f g

-- Test the resp function
test-resp : {S T : Setoid l0 l0} {f g : ≈.Hom S T} (f≈g : f ≈h g) →
           F̃-mor f ≈h F̃-mor g
test-resp f≈g = F̃-resp f≈g

-- Try to expose any hidden metas by being more explicit
test-explicit : {S T U : Setoid l0 l0} (f : ≈.Hom S T) (g : ≈.Hom T U) →
               {x y : Setoid.Carrier (F̃-ob S)} →
               (F̃-ob S Setoid.≈ x) y →
               (F̃-ob U Setoid.≈ (F̃-mor (g ≈.∘ f) Hom.⟦ x ⟧))
                                    ((F̃-mor g ≈.∘ F̃-mor f) Hom.⟦ y ⟧)
test-explicit f g = F̃-comp f g
