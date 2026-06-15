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

Fin-suc-injectiveˢ : ∀ {m} {a : Fin m} {b : Fin m}
                   → suc a ≡ˢ suc b → a ≡ˢ b
Fin-suc-injectiveˢ reflˢ = reflˢ

_≟Finˢ_ : ∀ {n} → Discreteˢ (Fin n)
zero ≟Finˢ zero = yes reflˢ
zero ≟Finˢ suc j = no (λ ())
suc i ≟Finˢ zero = no (λ ())
suc i ≟Finˢ suc j = case i ≟Finˢ j of
  λ{(no ¬p) → no λ q → ¬p (Fin-suc-injectiveˢ q)
  ; (yes p) → yes (congˢ suc p) }

_≟Fin_ : ∀ {n} → Discrete (Fin n)
_≟Fin_ = Discreteˢ→Discrete _≟Finˢ_
