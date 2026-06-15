{-# OPTIONS --injective-type-constructors #-}

module QIT.Prop.SetPath where

open import QIT.Prelude
open import QIT.Prop.Path public using (_≡ᵖ_; ≡→≡ˢ; ≡ˢ→≡)

open import Relation.Binary.PropositionalEquality.Core
  renaming (_≡_ to _≡ˢ_; refl to reflˢ; cong to congˢ; subst to substˢ) public
open import Relation.Binary.PropositionalEquality.Properties
  using () renaming (J to Jˢ)
  public

postulate
  funExtˢ : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
           → (∀ x → f x ≡ˢ g x) → f ≡ˢ g

symˢ : ∀ {ℓA} {A : Set ℓA} {x y : A} → x ≡ˢ y → y ≡ˢ x
symˢ reflˢ = reflˢ

transˢ : ∀ {ℓA} {A : Set ℓA} {x y z : A} → x ≡ˢ y → y ≡ˢ z → x ≡ˢ z
transˢ reflˢ reflˢ = reflˢ

subst-idˢ : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
          → {x : A} (p : x ≡ˢ x) (b : B x)
          → substˢ B p b ≡ˢ b
subst-idˢ reflˢ b = reflˢ

subst-constˢ : ∀ {ℓA ℓB} {A : Set ℓA} (B : Set ℓB)
             → ∀ {x y : A} (z : B) (p : x ≡ˢ y)
             → substˢ (λ _ → B) p z ≡ˢ z
subst-constˢ B z reflˢ = reflˢ

cong₂ˢ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
       → ∀ {a1 a2 b1 b2} → a1 ≡ˢ a2 → b1 ≡ˢ b2 → f a1 b1 ≡ˢ f a2 b2
cong₂ˢ f reflˢ reflˢ = reflˢ

subst₂ˢ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Set ℓC)
       → {a1 a2 : A} {b1 b2 : B}
       → (p : a1 ≡ˢ a2) (q : b1 ≡ˢ b2)
       → C a1 b1 → C a2 b2
subst₂ˢ C reflˢ reflˢ x = x

funExtˢ⁻ : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
         → f ≡ˢ g → (∀ x → f x ≡ˢ g x)
funExtˢ⁻ reflˢ _ = reflˢ

module ≡ˢ-Reasoning {ℓ} {A : Set ℓ} where
  infix 1 begin_
  begin_ : ∀ {x y : A} → x ≡ˢ y → x ≡ˢ y
  begin p = p

  infixr 2 step-≡
  step-≡ : ∀ (x : A) {y z} → y ≡ˢ z → x ≡ˢ y → x ≡ˢ z
  step-≡ _ q p = transˢ p q
  syntax step-≡ x q p = x ≡⟨ˢ p ⟩ q

  infix 3 _∎
  _∎ : ∀ (x : A) → x ≡ˢ x
  x ∎ = reflˢ
