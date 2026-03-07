module QIT.Relation.Nullary where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Function.Base 
open import QIT.Fin
open import Data.Fin
open import Data.Nat

module _ {ℓA} where
  isFiniteᵖ : (A : Set ℓA) → Prop _
  isFiniteᵖ A = ∃ λ n → ∥ Fin n ↠ A ∥ 

  isFinite : (A : Set ℓA) → Set _
  isFinite A = Σ ℕ λ n → Fin n ↔ A

  isFinite→Discrete : (A : Set ℓA) → isFinite A → Discrete A
  isFinite→Discrete A (n , f) x y =
    case (i ≟ꟳ j) of
      λ{(no ¬p) → no (λ q → ¬p (≡.cong from q) )
      ; (yes p) → yes (≡.trans (≡.sym (linv x)) (≡.trans (≡.cong to p) (linv y))) }  
    where
    open _↔_ f
    i = from x
    j = from y

FinSet : ∀ ℓA → Set (lsuc ℓA)
FinSet ℓA = Σ (Set ℓA) isFinite

