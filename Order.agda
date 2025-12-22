{-# OPTIONS --type-in-type #-}
module Order where

open import Prelude
open import Data.Product
open import Equivalence

module _ {ℓA ℓ<} {A : Set ℓA} (_<_ : A → A → Prop ℓ<) where
    WfRec : (A → Prop (ℓA ⊔ ℓ<)) → (A → Prop (ℓA ⊔ ℓ<))
    WfRec P x = ∀ y → y < x → P y

    data Acc (x : A) : Prop (ℓA ⊔ ℓ<) where
      acc : (rs : WfRec Acc x) → Acc x

    WellFounded : Prop _
    WellFounded = ∀ x → Acc x

record IsPreorder {ℓS ℓ≤} {S : Set ℓS} (_≤_ : Rel S ℓ≤) : Set (ℓS ⊔ ℓ≤) where
  field
    refl  : Reflexive _≤_
    trans : Transitive _≤_

Preorder : ∀ {ℓ} (S : Set ℓ) → ∀ ℓ'' → Set lzero
Preorder S ℓ'' = Σ (Rel S ℓ'') IsPreorder

IsWeaklyExtensional : ∀ {ℓA ℓ≤} {A : Set ℓA} (_≤_ _<_ : Rel A ℓ≤) → Prop
IsWeaklyExtensional {A = A} _≤_ _<_ = ∀ x y → x ≲ y → y ≲ x → x ≡p y 
  where
  _≲_ : (x y : A) → Prop
  x ≲ y = ∀ z → z < x → z < y

