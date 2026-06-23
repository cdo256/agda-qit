module CZF where

open import QIT.Prelude
open import QIT.Prop as P

infix 8 _∈_

postulate
  𝓤 : Set₁
  _∈_ : 𝓤 → 𝓤 → Prop₁

↓_ : 𝓤 → Set₁
↓ X = ΣP 𝓤 (_∈ X)

∃∈ : ∀ X → (𝓤 → Prop₁) → Prop₁
∃∈ X p = ∃ λ ((x , _) : ↓ X) → p x
syntax ∃∈ X (λ x → p) = ∃ˢ x ∈ X ∙ p

∀∈ : ∀ X → (𝓤 → Prop₁) → Prop₁
∀∈ X p = ∀ ((x , _) : ↓ X) → p x
syntax ∀∈ X (λ x → p) = ∀ˢ x ∈ X ∙ p

postulate
  ext : ∀ X Y → (∀ x → x ∈ X ⇔ x ∈ Y) → X ≡ Y
  ∅ : 𝓤
  ∈∅e : ∀ x → ¬ x ∈ ∅
  [_,_] : 𝓤 → 𝓤 → 𝓤
  ∈[,]e : ∀ x y z → z ∈ [ x , y ] → z ≡ x ∨ z ≡ y
  ∈[,]i₁ : ∀ x y → x ∈ [ x , y ]
  ∈[,]i₂ : ∀ x y → y ∈ [ x , y ]
  ⋃ : 𝓤 → 𝓤
  ∈⋃i : ∀ X → ∀ x Y → x ∈ Y → Y ∈ X → x ∈ ⋃ X
  ∈⋃e : ∀ X → ∀ x → x ∈ ⋃ X → ∃ λ Y → x ∈ Y → Y ∈ X

_⊆_ : 𝓤 → 𝓤 → Prop₁
X ⊆ Y = ∀ x → x ∈ X → x ∈ Y 

postulate
  𝓟 : 𝓤 → 𝓤
  ∈𝓟i : ∀ X Y → Y ⊆ X → Y ∈ 𝓟 X
  ∈𝓟e : ∀ X Y → Y ∈ 𝓟 X → Y ⊆ X
  ⟨∣⟩ : (X : 𝓤) → (𝓤 → Prop₁) → 𝓤
  ∈⟨∣⟩i : ∀ X P x → x ∈ X → P x → x ∈ ⟨∣⟩ X P
  ∈⟨∣⟩e₁ : ∀ X P x → x ∈ ⟨∣⟩ X P → x ∈ X
  ∈⟨∣⟩e₂ : ∀ X P x → x ∈ ⟨∣⟩ X P → P x

syntax ⟨∣⟩ X (λ x → P) = ⟨ x ∈ X ∣ P ⟩

_∪_ : 𝓤 → 𝓤 → 𝓤
X ∪ Y = ⋃ [ X , Y ]

_×ˢ_ : 𝓤 → 𝓤 → 𝓤
X ×ˢ Y = ⟨ Z ∈ 𝓟 (𝓟 (X ∪ Y)) ∣ (∃ˢ x ∈ X ∙ ∃ˢ y ∈ Y ∙ ([ x , y ] ≡ Z)) ⟩

_⇾_ : 𝓤 → 𝓤 → 𝓤
X ⇾ Y = ⟨ x ∈ X ×ˢ Y ∣ {!!} ⟩

postulate
  ⟨_∣ᵣ_⟩ : (X : 𝓤) (f : ↓ X → 𝓤) → 𝓤
  ∈⟨∣ᵣ⟩i : ∀ X f x → (x∈X : x ∈ X)
         → f (x , x∈X) ∈ ⟨ X ∣ᵣ f ⟩ 
  ∈⟨∣ᵣ⟩e : ∀ X f y → y ∈ ⟨ X ∣ᵣ f ⟩
         → ∃ λ x̂ → f x̂ ≡ y
  reg : ∀ A → (∀ x → x ∈ A → ∃ λ y → y ∈ A ∧ y ∈ x)
      → A ≡ ∅

zero : 𝓤
zero = ∅

suc : 𝓤 → 𝓤
suc x = x ∪ [ x , x ]

postulate
  ℕ : 𝓤
  0∈ℕi : zero ∈ ℕ
  s∈ℕi : ∀ n → n ∈ ℕ → suc n ∈ ℕ
  ∈ℕe : ∀ X → (zero ∈ X ∧ ∀ x → x ∈ X → suc x ∈ X) → ℕ ⊆ X

sup : 𝓤 → 𝓤
sup X = ⋃ X

ω : 𝓤
ω = ℕ

isOrd : 𝓤 → Prop₁ 
isOrd A = ∀ Y x → Y ∈ A → x ∈ Y → x ∈ A

-- _∩_ : 𝓤 → 𝓤 → 𝓤
-- X ∩ Y = ⟨ X ∣ _∈ Y ⟩

-- ⋂ : 𝓤 → 𝓤
-- ⋂ A = ⟨ ⋃ A ∣ (λ Y → ∀ x → Y ∈ A → x ∈ Y) ⟩

-- isOrd-∩ : ∀ X Y → isOrd X → isOrd Y → isOrd (X ∩ Y)
-- isOrd-∩ X Y isOrdX isOrdY Z x x∈Z Z∈X∩Y =
--   {!!}

-- isOrd-⋂ : ∀ A → (∀ Y → Y ∈ A → isOrd Y) → isOrd (⋂ A)
-- isOrd-⋂ A x Y x₁ x₂ x₃ = {!!}
