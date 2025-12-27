{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid
open import Data.Product

module QIT.Diagram {ℓI} {ℓ≤} {ℓB} {ℓB'}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  where

record Diagram : Set (ℓ≤ ⊔ lsuc ℓB ⊔ lsuc ℓB') where
  module ≤ = IsPreorder (≤p .proj₂)
  _≤_ : BinaryRel I ℓ≤
  _≤_ = ≤p .proj₁

  field
    D-ob : ∀ (i : I) → Setoid ℓB ℓB'
    D-mor : ∀ {i j} → (p : i ≤ j) → ≈.Hom (D-ob i) (D-ob j)
    D-id : ∀ {i : I}
         → ≈.Hom≈ (D-mor (≤.refl))
                  (≈.idHom {S = D-ob i})
    D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
           → ≈.Hom≈ (D-mor (≤.trans p q))
                    (D-mor q ≈.∘ D-mor p)
