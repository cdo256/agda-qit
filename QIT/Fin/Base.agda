module QIT.Fin.Base where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
open import Data.Fin as Fin hiding (_≟_; pred) public
open import Data.Nat hiding (_≟_)

ℕ-suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
ℕ-suc-injective = ≡.cong pred

Fin-suc-injective : ∀ {m} {a : Fin m} {b : Fin m}
                  → suc a ≡ suc b → a ≡ b
Fin-suc-injective ≡.refl = ≡.refl

_≟ℕ_ : Discrete ℕ
zero ≟ℕ zero = yes (box ≡.refl)
zero ≟ℕ suc m = no λ ()
suc n ≟ℕ zero = no λ ()
suc n ≟ℕ suc m = case n ≟ℕ m of
  λ{(no ¬p) → no λ (box q) → ¬p (box (ℕ-suc-injective q))
  ; (yes (box p)) → yes (box (≡.cong suc p))}

_≟Fin_ : ∀ {n} → Discrete (Fin n) 
zero ≟Fin zero = yes (box ≡.refl)
zero ≟Fin suc j = no (λ ())
suc i ≟Fin zero = no (λ ())
suc i ≟Fin suc j = case i ≟Fin j of
  λ{(no ¬p) → no λ (box q) → ¬p (box (Fin-suc-injective q))
  ; (yes (box p)) → yes (box (≡.cong suc p)) }
