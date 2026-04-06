open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Category.Base
open import QIT.Category.Strict

open import QIT.Set.Base

module QIT.Category.Preorder
  {ℓA ℓ≤} (A : Set ℓA) (≤p : Preorder A ℓ≤) where

private
  module ≤ = IsPreorder (≤p .proj₂)
  _≤_ : BinaryRel A ℓ≤
  _≤_ = ≤p .proj₁

  _≤ˢ_ : A → A → Set ℓ≤
  x ≤ˢ y = Box (x ≤ y)

PreorderStrCat : StrictCategory ℓA ℓ≤
PreorderStrCat = record
  { Obj = A
  ; _⇒_ = _≤ˢ_
  ; id = box ≤.refl
  ; _∘_ = λ g f → box (≤.trans (f .unbox) (g .unbox))
  ; assoc = ≡.isPropBox _ _
  ; sym-assoc = ≡.isPropBox _ _
  ; identityˡ = ≡.isPropBox _ _
  ; identityʳ = ≡.isPropBox _ _
  ; identity² = ≡.isPropBox _ _
  }
  where open Box

PreorderCat : Category ℓA ℓ≤ ℓ≤
PreorderCat = StrictCategory→Category PreorderStrCat
