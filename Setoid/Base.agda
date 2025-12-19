{-# OPTIONS --type-in-type #-}
module Setoid.Base where

open import Prelude
open import Data.Product
open import Equivalence
 
private
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level
  ℓ = lzero
  ℓ' = lzero
  ℓ'' = lzero
  ℓ''' = lzero
  ℓ'''' = lzero

record Setoid ℓ ℓ' : Set (lsuc (ℓ ⊔ ℓ')) where
  infix 4 _≈_
  field
    Carrier       : Set ℓ 
    _≈_           : Rel Carrier ℓ'
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

⟨_⟩ : Setoid ℓ ℓ' → Set ℓ
⟨ S ⟩ = S .Setoid.Carrier

_[_≈_] : (S : Setoid ℓ ℓ') → (x y : S .Setoid.Carrier) → Prop _
S [ x ≈ y ] = S .Setoid._≈_ x y

module ≈syntax {ℓ ℓ'} {S : Setoid ℓ ℓ'} where
  open Setoid S renaming (Carrier to A)

  infix 1 begin_

  begin_ : ∀ {x y} → x ≈ y → x ≈ y
  begin p = p

  step-≈ : ∀ (x : A) {y z} → y ≈ z → x ≈ y → x ≈ z
  step-≈ _ q p = trans p q
  syntax step-≈ x q p = x ≈⟨ p ⟩ q
  
  infix 3 _∎

  _∎ : ∀ x → x ≈ x
  x ∎ = refl

Rel≈ : (S : Setoid ℓ ℓ') → ∀ ℓ'' → Set (lsuc ℓ ⊔ lsuc ℓ'')
Rel≈ S ℓ'' = A → A → Prop (ℓ ⊔ ℓ'')
  where
  open Setoid S renaming (Carrier to A)

record IsPreorder (S : Setoid ℓ ℓ') (_≲_ : Rel≈ S ℓ'') : Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
  module S = Setoid S
  field
    refl  : ∀ {x y} → x S.≈ y → x ≲ y
    trans : Transitive _≲_

Preorder : (S : Setoid ℓ ℓ') → ∀ ℓ'' → Set lzero
Preorder S ℓ'' = Σ (Rel≈ S ℓ'') (IsPreorder S)

≡setoid : ∀ (B : Set ℓ) → Setoid ℓ ℓ
≡setoid B = record
  { Carrier = B
  ; _≈_ = _≡p_
  ; isEquivalence = isEquiv≡p B }
