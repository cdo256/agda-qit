module QIT.Setoid.Base where

open import QIT.Prelude
open import Data.Product
open import QIT.Relation.Base
open import QIT.Relation.Binary

record Setoid ℓ ℓ' : Set (lsuc (ℓ ⊔ ℓ')) where
  infix 4 _≈_
  field
    Carrier       : Set ℓ
    _≈_           : BinaryRel Carrier ℓ'
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

⟨_⟩ : ∀ {ℓ ℓ'} → Setoid ℓ ℓ' → Set ℓ
⟨ S ⟩ = S .Setoid.Carrier

_[_≈_] : ∀ {ℓ ℓ'} → (S : Setoid ℓ ℓ') → (x y : S .Setoid.Carrier) → Prop _
S [ x ≈ y ] = S .Setoid._≈_ x y

module ≈syntax {ℓ ℓ'} {S : Setoid ℓ ℓ'} where
  open Setoid S renaming (Carrier to A)

  infix 1 begin_

  begin_ : ∀ {x y} → x ≈ y → x ≈ y
  begin p = p

  infixr 2 step-≈
  step-≈ : ∀ (x : A) {y z} → y ≈ z → x ≈ y → x ≈ z
  step-≈ _ q p = trans p q
  syntax step-≈ x q p = x ≈⟨ p ⟩ q

  infix 3 _∎

  _∎ : ∀ x → x ≈ x
  x ∎ = refl

Rel≈ : ∀ {ℓ ℓ'} → (S : Setoid ℓ ℓ') → ∀ ℓ'' → Set (lsuc ℓ ⊔ lsuc ℓ'')
Rel≈ {ℓ} S ℓ'' = BinaryRel A (ℓ ⊔ ℓ'')
  where
  open Setoid S renaming (Carrier to A)


≡setoid : ∀ {ℓ} (B : Set ℓ) → Setoid ℓ ℓ
≡setoid B = record
  { Carrier = B
  ; _≈_ = _≡p_
  ; isEquivalence = isEquiv-≡p B }

≡→≈ : ∀ {ℓ ℓ'} → (A : Setoid ℓ ℓ') → {x y : ⟨ A ⟩} → x ≡ y → A [ x ≈ y ]
≡→≈ A {x} p = substp (λ ○ → x ≈ ○) p refl
  where open Setoid A
