{-# OPTIONS --injective-type-constructors #-}

open import QIT.Prelude

module QIT.Prop.HetPath ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Identity

private
  variable
    a b c : Level
    A : Set a

infix 4 _≣_

data _≣_ {A : Set a} (x : A) : {B : Set b} → B → Prop a where
   refl : x ≣ x

≣-to-≡ : ∀ {x y : A} → x ≣ y → x ≡ y
≣-to-≡ refl = refl

≡-to-≣ : ∀ {x y : A} → x ≡ y → x ≣ y
≡-to-≣ refl = refl

sym : ∀ {A : Set a} {x : A} {B : Set b} {y : B}
    → x ≣ y → y ≣ x
sym refl = refl

trans : ∀ {A : Set a} {x : A} {B : Set b} {y : B} {C : Set c} {z : C}
      → x ≣ y → y ≣ z → x ≣ z
trans refl refl = refl
