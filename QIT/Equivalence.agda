{-# OPTIONS --type-in-type #-}
module QIT.Equivalence where

open import QIT.Prelude
open import Data.Product

private
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level
  ℓ = lzero
  ℓ' = lzero
  ℓ'' = lzero
  ℓ''' = lzero
  ℓ'''' = lzero


Reflexive : ∀ {ℓ'} → {A : Set ℓ} (_≈_ : Rel A ℓ') → Prop (ℓ ⊔ ℓ')
Reflexive _≈_ = ∀ {x} → x ≈ x

Symmetric : ∀ {ℓ'} → {A : Set ℓ} (_≈_ : Rel A ℓ') → Prop (ℓ ⊔ ℓ')
Symmetric _≈_ = ∀ {x y} → x ≈ y → y ≈ x

Transitive : ∀ {ℓ'} → {A : Set ℓ} (_≈_ : Rel A ℓ') → Prop (ℓ ⊔ ℓ')
Transitive _≈_ = ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

record IsEquivalence {ℓ'} {A : Set ℓ} (_≈_ : Rel A ℓ') : Prop (ℓ' ⊔ ℓ) where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

isEquiv≡p : ∀ (A : Set ℓ) → IsEquivalence (_≡p_ {A = A})
isEquiv≡p A = record { refl = ∣ refl ∣ ; sym = sym ; trans = trans }
  where
  open _≡_
  sym : Symmetric (Trunc₂ _≡_)
  sym ∣ refl ∣ = ∣ refl ∣
  trans : Transitive (Trunc₂ _≡_)
  trans ∣ refl ∣ ∣ refl ∣ = ∣ refl ∣
