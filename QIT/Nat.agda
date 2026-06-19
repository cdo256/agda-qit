open import QIT.Prelude

module QIT.Nat where

open import QIT.Prop
-- open import QIT.Relation.Base
-- open import QIT.Relation.Subset
-- open import QIT.Relation.Nullary
-- open import QIT.Function.Base 

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_) renaming (Nat to ℕ; _-_ to _∸_)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

ℕ-suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
ℕ-suc-injective = ≡.cong pred

_≟ℕ_ : Discrete ℕ
zero ≟ℕ zero = yes ≡.refl
zero ≟ℕ suc m = no λ ()
suc n ≟ℕ zero = no λ ()
suc n ≟ℕ suc m = case n ≟ℕ m of
  λ{(no ¬p) → no λ q → ¬p (ℕ-suc-injective q)
  ; (yes p) → yes (≡.cong suc p)}

iter : ∀ {ℓX} {X : Set ℓX} → X → (X → X) → ℕ → X
iter z s zero = z
iter z s (suc n) = s (iter z s n)

+suc : ∀ m n → m + suc n ≡ suc (m + n)
+suc zero n = ≡.refl
+suc (suc m) n = ≡.cong suc (+suc m n)

infix 4 _≤_ _<_ _≥_ _>_

data _≤_ : ℕ → ℕ → Prop where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : ℕ → ℕ → Prop
m < n = suc m ≤ n

_>_ : ℕ → ℕ → Prop
m > n = n < m

_≥_ : ℕ → ℕ → Prop
m ≥ n = n ≤ m

≤-total : ∀ m n → m ≤ n ∨ n ≤ m
≤-total zero zero = ∨.inl z≤n
≤-total zero (suc n) = ∨.inl z≤n
≤-total (suc m) zero = ∨.inr z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | ∨.inl p = ∨.inl (s≤s p)
... | ∨.inr q = ∨.inr (s≤s q)

