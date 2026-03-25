{-# OPTIONS --injective-type-constructors #-}

module QIT.Prop.HetPath where

open import QIT.Prelude
open import QIT.Prop.Path

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
