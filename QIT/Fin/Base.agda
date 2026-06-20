module QIT.Fin.Base where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Nat

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)

inject₁ : ∀ {n} → Fin n → Fin (suc n)
inject₁ = suc

fromℕ : ∀ n → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

Fin-suc-injective : ∀ {m} {a : Fin m} {b : Fin m}
                  → suc a ≡ suc b → a ≡ b
Fin-suc-injective ≡.refl = ≡.refl

_≟Fin_ : ∀ {n} → Discrete (Fin n) 
zero ≟Fin zero = yes ≡.refl
zero ≟Fin suc j = no (λ ())
suc i ≟Fin zero = no (λ ())
suc i ≟Fin suc j = case i ≟Fin j of
  λ{(no ¬p) → no λ q → ¬p (Fin-suc-injective q)
  ; (yes p) → yes (≡.cong suc p) }
