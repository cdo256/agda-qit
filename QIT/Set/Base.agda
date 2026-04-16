open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary

module QIT.Set.Base where

module ≡syntax {ℓ} {A : Set ℓ} where

  infix 1 begin_
  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin p = p

  infixr 2 step-≡
  step-≡ : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ q p = ≡.trans p q
  syntax step-≡ x q p = x ≡⟨ p ⟩ q

  infix 3 _∎
  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = ≡.refl

infixr 5 _∘_
_∘_ : ∀ {ℓA ℓB ℓC}
    → {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
    → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

id : ∀ {ℓA} {A : Set ℓA} → A → A
id x = x

infix 4 _≡h_
_≡h_ : ∀ {ℓA ℓB}
    → {A : Set ℓA} {B : Set ℓB}
    → (f g : A → B) → Prop (ℓA ⊔ ℓB)
f ≡h g = ∀ {x} → f x ≡ g x

isEquiv-≡h : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
        → IsEquivalence (_≡h_ {A = A} {B})
isEquiv-≡h = record
  { refl = ≡.refl
  ; sym = λ p → ≡.sym p
  ; trans = λ p q → ≡.trans p q }

∘-resp-≡h : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
          → {f h : B → C} {g i : A → B}
          → f ≡h h → g ≡h i → f ∘ g ≡h h ∘ i
∘-resp-≡h {h = h} p q {x} = ≡.trans p (≡.cong h q)
