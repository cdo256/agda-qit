module QIT.Relation.Finite where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
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

  -- Discrete types - equality is decidable.
  Discrete : ∀ {ℓA} (A : Set ℓA) → Set ℓA
  Discrete A = ∀ (x y : A) → Dec (x ≡ y)

  -- Conditional expression based on decidability.
  infixr 3 if_then_else_
  if_then_else_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (decA : Dec A) → B → B → B
  if yes _ then b else b' = b
  if no _ then b else b' = b'

  const : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (a : A) → B → A
  const a _ = a

  isProp : ∀ {ℓA} → Set ℓA → Set ℓA
  isProp A = ∀ (x y : A) → x ≡ y

  isContr : ∀ {ℓA} → Set ℓA → Set ℓA
  isContr A = Σ A λ x → ∀ y → x ≡ y

  Σ≡Prop
    : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
    → ((x : A) → isProp (B x)) → {u v : Σ A B}
    → (p : u .proj₁ ≡ v .proj₁) → u ≡ v
  Σ≡Prop pB {x , u} {x , v} ≡.refl = ≡.cong (x ,_) (pB x u v)

  isSetSet : ∀ {ℓA} {A : Set ℓA} {x y : A} (p q : x ≡ y) → p ≡ q
  isSetSet ≡.refl ≡.refl = ≡.refl
