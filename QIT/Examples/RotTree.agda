module QIT.Examples.RotTree (A : Set) where

open import QIT.Prelude
open import QIT.Container.Base
open import QIT.QW
open import Data.Nat
open import Data.Fin
open import Data.Vec

data Sᵀ : Set where
  l : A → Sᵀ
  n : Sᵀ

Pᵀ : Sᵀ → Set
Pᵀ (l x) = ⊥
Pᵀ n = Fin 2

-- Plain lists
T = W Sᵀ Pᵀ

branchᴱ : ∀ {V : Set} (s t : QW.Expr Sᵀ Pᵀ ℓ0 V) → QW.Expr Sᵀ Pᵀ ℓ0 V
branchᴱ s t = QW.supᴱ n (lookup (s ∷ t ∷ []))

var : ∀ {V : Set} (v : V) → QW.Expr Sᵀ Pᵀ ℓ0 V
var v = QW.varᴱ v {λ()}

rot : QW.Equation Sᵀ Pᵀ ℓ0
rot = record
  { V = Fin 3
  ; lhs = branchᴱ sⱽ (branchᴱ tⱽ uⱽ)
  ; rhs = branchᴱ (branchᴱ sⱽ tⱽ) uⱽ }
  where
  sⱽ = var zero
  tⱽ = var (suc zero)
  uⱽ = var (suc (suc zero))
  

RotTree : QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
RotTree = record
  { S = Sᵀ
  ; P = Pᵀ
  ; E = ⊤
  ; Ξ = λ _ → rot }
