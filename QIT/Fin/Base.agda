module QIT.Fin.Base where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
open import Data.Fin as Fin hiding (_≟_; pred) public
open import QIT.Nat

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
