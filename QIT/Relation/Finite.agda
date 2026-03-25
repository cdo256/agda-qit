module QIT.Relation.Finite where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
open import QIT.Fin.Base
open import Data.Nat

module _ {ℓA} where
  isFiniteᵖ : (A : Set ℓA) → Prop _
  isFiniteᵖ A = ∃ λ n → ∥ Fin n ↠ A ∥ 

  isFinite : (A : Set ℓA) → Set _
  isFinite A = Σ ℕ λ n → Fin n ↔ A

  FinSet : Set (lsuc ℓA)
  FinSet = Σ (Set ℓA) isFinite

  isFinite→Discrete : (A : Set ℓA) → isFinite A → Discrete A
  isFinite→Discrete A (n , f) x y =
    case (i ≟Fin j) of
      λ{(no ¬p) → no (λ q → ¬p (box (≡.cong from (unbox q))) )
      ; (yes (box p)) → yes (box (≡.trans (≡.sym (linv x)) (≡.trans (≡.cong to p) (linv y)))) }  
    where
    open _↔_ f
    i = from x
    j = from y
