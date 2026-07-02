open import QIT.Prelude

module QIT.Relation.Finite
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
open import QIT.Fin.Base
open import QIT.Fin.Properties
open import QIT.Set.Bijection
open import QIT.Nat

module _ {ℓA} where
  isFiniteᵖ : (A : Set ℓA) → Prop _
  isFiniteᵖ A = ∃ λ n → ∥ Fin n ≅ˢ A ∥

  isFinite' : (A : Set ℓA) → Set _
  isFinite' A = ΣP ℕ λ n → ∥ Fin n ≅ˢ A ∥

  isFinite : (A : Set ℓA) → Set _
  isFinite A = Σ ℕ λ n → Fin n ≅ˢ A

  FinSet : Set (lsuc ℓA)
  FinSet = Σ (Set ℓA) isFinite

  isFinite→Discrete : (A : Set ℓA) → isFinite A → Discrete A
  isFinite→Discrete A (n , f) x y =
    case (i ≟Fin j) of
      λ{(no ¬p) → no (λ q → ¬p (≡.cong from q) )
      ; (yes p) → yes (≡.trans (≡.sym (linv x)) (≡.trans (≡.cong to p) (linv y))) }  
    where
    open _≅ˢ_ f
    i = from x
    j = from y

  isFiniteᵖ→isFinite' : (a!c : A!C) {A : Set ℓA} → isFiniteᵖ A → isFinite' A
  isFiniteᵖ→isFinite' a!c {A} isFiniteA = 
    A!C.a!c a!c _ isContrΣSz
    where
    Sz : (n : ℕ) → Prop ℓA
    Sz n = ∥ Fin n ≅ˢ A ∥
    isPropΣSz : isProp (ΣP ℕ Sz)
    isPropΣSz (m , ∣ p ∣) (n , ∣ q ∣) = ΣP≡ _ _ m≡n
      where
      open ≅ˢ
      [m]↔[n] : Fin m ≅ˢ Fin n
      [m]↔[n] = sym q ∘ p
      m≡n : m ≡ n
      m≡n = cantor-schröder-bernstein
        ([m]↔[n] .to) ([m]↔[n] .from)
        (≅-to-Injection [m]↔[n])
        (≅-to-Injection (sym [m]↔[n]))
    isContrΣSz : isContr (ΣP ℕ Sz)
    isContrΣSz = mkIsContr _ (∃e (λ n p → ∣ (n , p) ∣) isFiniteA) isPropΣSz
