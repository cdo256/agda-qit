open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Category.Base

open import QIT.Set.Base

module QIT.Category.Preorder
  {ℓA ℓ≤} (A : Set ℓA) (≤p : Preorder A ℓ≤) where

private
  module ≤ = IsPreorder (≤p .proj₂)
  _≤_ : BinaryRel A ℓ≤
  _≤_ = ≤p .proj₁

  _≤ˢ_ : A → A → Set ℓ≤
  x ≤ˢ y = Box (x ≤ y)

PreorderCat : Category ℓA ℓ≤ ℓ≤
PreorderCat = record
  { Obj = A
  ; _⇒_ = _≤ˢ_
  ; _≈_ = _≡p_
  ; id = box ≤.refl
  ; _∘_ = λ g f → box (≤.trans (f .unbox) (g .unbox))
  ; assoc = reflp
  ; sym-assoc = reflp
  ; identityˡ = reflp
  ; identityʳ = reflp
  ; identity² = reflp
  ; equiv = λ {A B} → isEquiv-≡p (A ≤ˢ B)
  ; ∘-resp-≈ = λ{ reflp reflp → reflp }
  }
  where open Box
