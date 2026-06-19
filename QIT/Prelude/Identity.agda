{-# OPTIONS --injective-type-constructors #-}
module QIT.Prelude.Identity where

infix 4 _≡_
data _≡_ {ℓ} {A : Set ℓ} : (x y : A) → Prop ℓ where
  refl : ∀ {x} → x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

data _≡ᵖ_ {ℓA} {A : Prop ℓA} : (x y : A) → Prop ℓA where
   refl : ∀ {x} → x ≡ᵖ x

data _≡ˢ_ {ℓA} {A : Set ℓA} : (x y : A) → Set ℓA where
  reflˢ : ∀ {x} → x ≡ˢ x
