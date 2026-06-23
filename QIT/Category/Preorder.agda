open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Category.Base
open import QIT.Category.Strict
open import QIT.Functor.Base
open import QIT.Relation.Subset

open import QIT.Set.Base

module QIT.Category.Preorder ⦃ pathElim* : PathElim ⦄
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

Below : A → Set (ℓA ⊔ ℓ≤)
Below x = ΣP A (λ y → y ≤ x)

_≤↓_ : ∀ {x} → BinaryRel (Below x) ℓ≤
_≤↓_ {x} a b = a .fst ≤ b .fst

Restrict≤ : (x : A) → Preorder (Below x) ℓ≤
Restrict≤ x = _≤↓_ , record
  { refl = ≤.refl
  ; trans = ≤.trans
  }

PreorderStrCat↓ : (x : A) → StrictCategory (ℓA ⊔ ℓ≤) ℓ≤
PreorderStrCat↓ x = record
  { Obj = Below x
  ; _⇒_ = λ a b → Box (a .fst ≤ b .fst)
  ; id = box ≤.refl
  ; _∘_ = λ g f → box (≤.trans (f .unbox) (g .unbox))
  ; assoc = ≡.isPropBox _ _
  ; sym-assoc = ≡.isPropBox _ _
  ; identityˡ = ≡.isPropBox _ _
  ; identityʳ = ≡.isPropBox _ _
  ; identity² = ≡.isPropBox _ _
  }
  where open Box

PreorderCat↓ : (x : A) → Category (ℓA ⊔ ℓ≤) ℓ≤ ℓ≤
PreorderCat↓ x = StrictCategory→Category (PreorderStrCat↓ x)

include≤ : (x : A) → Functor (PreorderCat↓ x) PreorderCat
include≤ x = record
  { ob = λ y → y .fst
  ; hom = λ p → p
  ; id = ≡.isPropBox _ _
  ; comp = λ _ _ → ≡.isPropBox _ _
  ; resp = λ _ → ≡.isPropBox _ _
  }
