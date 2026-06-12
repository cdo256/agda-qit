module QIT.Nat where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
open import Data.Nat public

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
