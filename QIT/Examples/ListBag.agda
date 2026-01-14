module QIT.Examples.ListBag (A : Set) where

open import QIT.Prelude
open import QIT.Container.Base
open import QIT.QW

data Sᵀ : Set where
  []ˢ : Sᵀ
  _∷ˢ : A → Sᵀ

Pᵀ : Sᵀ → Set
Pᵀ []ˢ = ⊥
Pᵀ (x ∷ˢ) = ⊤

-- Plain lists
T = W Sᵀ Pᵀ

swap : A × A → QW.Equation Sᵀ Pᵀ ℓ0
swap (x , y) = record
  { V = ⊤
  ; lhs = QW.supᴱ (x ∷ˢ) λ _ → QW.supᴱ (y ∷ˢ) λ _ → QW.varᴱ tt {λ()}
  ; rhs = QW.supᴱ (y ∷ˢ) λ _ → QW.supᴱ (x ∷ˢ) λ _ → QW.varᴱ tt {λ()} }

contraction : A → QW.Equation Sᵀ Pᵀ ℓ0
contraction x = record 
  { V = ⊤
  ; lhs = QW.supᴱ (x ∷ˢ) λ _ → QW.supᴱ (x ∷ˢ) λ _ → QW.varᴱ tt {λ()}
  ; rhs = QW.supᴱ (x ∷ˢ) λ _ → QW.varᴱ tt {λ()} }

Bag : QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
Bag = record
  { S = Sᵀ
  ; P = Pᵀ
  ; E = A × A
  ; Ξ = swap }

FinSet : QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
FinSet = record
  { S = Sᵀ
  ; P = Pᵀ
  ; E = (A × A) ⊎ A
  ; Ξ = ⊎.[ swap , contraction ] }

