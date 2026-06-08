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
      λ{(no ¬p) → no (λ q → ¬p (≡.cong from q) )
      ; (yes p) → yes (≡.trans (≡.sym (linv x)) (≡.trans (≡.cong to p) (linv y))) }  
    where
    open _↔_ f
    i = from x
    j = from y

  isFiniteᵖ→isFinite : {A : Set ℓA} → isFiniteᵖ A → isFinite A
  isFiniteᵖ→isFinite {A} isFiniteA = {!!} , {!!}
    where
    Sz : (n : ℕ) → Prop ℓA
    Sz n = ∥ Fin n ↔ A ∥
    isPropΣSz : isProp (ΣP ℕ Sz)
    isPropΣSz (m , ∣ p ∣) (n , ∣ q ∣) = ΣP≡ _ _ m≡n
      where
      open ↔
      open import QIT.Fin.Properties
      [m]↔[n] : Fin m ↔ Fin n
      [m]↔[n] = flip q ∘ p
      m≡n : m ≡ n
      m≡n = cantor-schröder-bernstein
        ([m]↔[n] .to) ([m]↔[n] .from)
        (↔to-Injection [m]↔[n])
        (↔to-Injection (flip [m]↔[n]))
    isContrΣSz : isContr (ΣP ℕ Sz)
    isContrΣSz = ∣ {!!} , isPropΣSz {!!} ∣
