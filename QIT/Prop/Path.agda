{-# OPTIONS --injective-type-constructors #-}

module QIT.Prop.Path where

open import QIT.Prelude

infix 4 _≡_
data _≡_ {ℓ} {A : Set ℓ} : (x y : A) → Prop ℓ where
  refl : ∀ {x} → x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

postulate
  funExt : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
          → (∀ x → f x ≡ g x) → f ≡ g
  subst : ∀ {ℓA ℓB} {A : Set ℓA} (B : A → Set ℓB) {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
  subst-id : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
           → {x : A} (p : x ≡ x) (b : B x)
           → subst B p b ≡ b
  subst-const : ∀ {ℓA ℓB ℓP} {A : Set ℓA} {B : Set ℓB} (P : Set ℓP)
              → ∀ {x : B} (z : P) (p : x ≡ x)
              → subst (λ _ → P) p z ≡ z
  J : ∀ {ℓA ℓB} {A : Set ℓA} {x : A}
    → (B : (y : A) → x ≡ y → Set ℓB)
    → {y : A} (p : x ≡ y) → B x refl → B y p


{-# REWRITE subst-id #-}

Jp : ∀ {ℓA ℓB} {A : Set ℓA} {x : A}
  → (B : (y : A) → x ≡ y → Prop ℓB)
  → {y : A} (p : x ≡ y) → B x refl → B y p
Jp B refl x = x

open import Agda.Builtin.Equality public
  renaming (_≡_ to _≡ˢ_; refl to reflˢ)

≡ˢ→≡ : ∀ {ℓA} {A : Set ℓA} {x y : A} → x ≡ˢ y → x ≡ y
≡ˢ→≡ reflˢ = refl

≡→≡ˢ : ∀ {ℓA} {A : Set ℓA} {x y : A} → x ≡ y → x ≡ˢ y
≡→≡ˢ {x = x} {y} p = J (λ y p → x ≡ˢ y) p reflˢ
