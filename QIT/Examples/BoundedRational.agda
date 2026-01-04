module QIT.Examples.BoundedRational where

open import QIT.Prelude
open import QIT.Relation.Subset
open import Data.Nat as ℕ
open import Data.Empty as ⊥
open import Data.Product hiding (∃)

IsMonotone : {A : Set} (_<_ : A → A → Prop) (f : ℕ → A) → Prop
IsMonotone _<_ f = ∀ i j → i ℕ.< j → f i < f j

Monotone : {A : Set} (_<_ : A → A → Prop) → Set
Monotone {A = A} _<_ = ΣP (ℕ → A) (IsMonotone _<_)

mutual
  data Ord : Set where
    zero : Ord
    suc : Ord → Ord
    lim : ∀ δ → Monotone _<⟨ δ ⟩_ → Ord

  -- data _<⟨_⟩_ : Ord → ℕ → Ord → Prop where
  --   <suc  : ∀ {δ x} → x <⟨ suc δ ⟩ suc x
  --   <lim  : ∀ {δ ζ f n} → f .fst n <⟨ suc δ + ζ ⟩ lim ζ f
  --   <step : ∀ {δ ζ x y z} → x <⟨ δ ⟩ y → y <⟨ ζ ⟩ z → x <⟨ δ ℕ.⊔ ζ ⟩ z
  --   <weaken : ∀ {δ ζ x y} → x <⟨ δ ⟩ y → δ ℕ.≤ ζ → x <⟨ ζ ⟩ y

  _<⟨_⟩_ : Ord → ℕ → Ord → Prop
  x <⟨ α ⟩ zero = ⊥p
  x <⟨ α ⟩ suc y = x <⟨ α ⟩ y
  x <⟨ α ⟩ lim δ f = ∃ (λ i → x <⟨ suc α ⟩ (f .fst i))


_≤⟨_⟩_ : Ord → ℕ → Ord → Prop
x ≤⟨ δ ⟩ y = ∀ z → z <⟨ δ ⟩ x → z <⟨ δ ⟩ y

ext : ℕ → Ord → Set
ext δ x = ΣP Ord (_<⟨ δ ⟩ x)

data _≈⟨_⟩_ : Ord → ℕ → Ord → Prop where
  ≈ext : ∀ {δ x y} → x ≤⟨ δ ⟩ y → y ≤⟨ δ ⟩ x → x ≈⟨ δ ⟩ y

_ : zero ≈⟨ 1 ⟩ zero
_ = ≈ext (λ _ x → x) (λ _ x → x)

cong-suc-≤ : ∀ δ x y → x ≤⟨ δ ⟩ y → suc x ≤⟨ suc δ ⟩ suc y
cong-suc-≤ δ x y x≤y zero z<sucx = {!!}
cong-suc-≤ δ x y x≤y (suc z) z<sucx = {!!}
cong-suc-≤ δ x y x≤y (lim δ₁ x₁) z<sucx = {!!}

≈refl : ∀ x α → x ≈⟨ α ⟩ x
≈refl _ _ = ≈ext (λ _ x → x) (λ _ x → x)

<trans : ∀ {α β x y z} → x <⟨ α ⟩ y → y <⟨ β ⟩ z → x <⟨ α ℕ.⊔ β ⟩ z
<trans _ q = q

≤trans : ∀ {α β x y z} → x ≤⟨ α ⟩ y → y ≤⟨ β ⟩ z → x ≤⟨ α ℕ.⊔ β ⟩ z
≤trans p q = λ u v → q u (p u v)

≈trans : ∀ {α β x y z} → x ≈⟨ α ⟩ y → y ≈⟨ β ⟩ z → x ≈⟨ α ℕ.⊔ β ⟩ z
≈trans (≈ext x≤y y≤x) (≈ext y≤z z≤y) =
  ≈ext (≤trans x≤y y≤z) (≤trans z≤y y≤x)

-- cong-suc : ∀ δ x y → x ≈⟨ δ ⟩ y → suc x ≈⟨ suc δ ⟩ suc y
-- cong-suc δ x y (≈ext x≤y y≤x) = ≈ext {!!} {!!}
