open import QIT.Prelude

module QIT.Nat where

open import QIT.Prop
-- open import QIT.Relation.Base
-- open import QIT.Relation.Subset
-- open import QIT.Relation.Nullary
-- open import QIT.Function.Base 

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

open import Agda.Builtin.Nat public
  using (_+_; _*_) renaming (_-_ to _∸_)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

-- ℕ-suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
-- ℕ-suc-injective = ≡.cong pred

-- _≟ℕ_ : Discrete ℕ
-- zero ≟ℕ zero = yes ≡.refl
-- zero ≟ℕ suc m = no λ ()
-- suc n ≟ℕ zero = no λ ()
-- suc n ≟ℕ suc m = case n ≟ℕ m of
--   λ{(no ¬p) → no λ q → ¬p (ℕ-suc-injective q)
--   ; (yes p) → yes (≡.cong suc p)}

-- iter : ∀ {ℓX} {X : Set ℓX} → X → (X → X) → ℕ → X
-- iter z s zero = z
-- iter z s (suc n) = s (iter z s n)

-- -- 0-right-identity : ∀ {n : ℕ} → n + 0 ≡ n
-- -- 0-right-identity {zero} = ≡.refl
-- -- 0-right-identity {suc n} =
-- --   ≡.cong suc 0-right-identity

-- -- +suc : ∀ m n → m + suc n ≡ suc (m + n)
-- -- +suc zero n = ≡.refl
-- -- +suc (suc m) n = ≡.cong suc (+suc m n)
