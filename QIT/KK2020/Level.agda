module QIT.KK2020.Level where

open import QIT.Prelude

-- Subtype relation
postulate
  _≤ᵁ_ : ∀ {i j} → Set i → Set j → Prop (i ⊔ j)
  univCumulative : ∀ {i j : Level} → Set i ≤ᵁ Set j
  piCumulative : ∀ {i j k} {A : Set k} (B : A → Set i) (B' : A → Set j) → (∀ x → B x) ≤ᵁ (∀ x → B' x)
  sigmaCumulative : ∀ {i j k} {A : Set k} (B : A → Set i) (B' : A → Set j) → Σ A B ≤ᵁ Σ A B'
  cumulativeRefl : ∀ {i} {A : Set i} → A ≤ᵁ A
  cumulativeTrans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → A ≤ᵁ B → B ≤ᵁ C → A ≤ᵁ C

-- Cumulative lift operator
postulate
  liftᵁ : ∀ {i j} {A : Set i} {A' : Set j} → A ≤ᵁ A' → A → A'
  liftRefl : ∀ {i} {A : Set i} (t : A) → liftᵁ cumulativeRefl t ≡ t
  liftTrans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
    (p : A ≤ᵁ B) (q : B ≤ᵁ C) (r : A ≤ᵁ C) (t : A) →
    liftᵁ q (liftᵁ p t) ≡ liftᵁ r t
  liftPi : ∀ {i j k} {A : Set k} {B : A → Set i} {B' : A → Set j}
    (p : ∀ x → B x ≤ᵁ B' x)
    (q : (∀ x → B x) ≤ᵁ (∀ x → B' x))
    (f : ∀ x → B x) (x : A) →
    liftᵁ q f x ≡ liftᵁ (p x) (f x)
  liftInjective : ∀ {i j} {A : Set i} {A' : Set j} (p : A ≤ᵁ A') {x y : A} →
    liftᵁ p x ≡ liftᵁ p y → x ≡ y
