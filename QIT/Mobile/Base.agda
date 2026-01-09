module QIT.Mobile.Base (I : Set) where

open import QIT.Prelude
open import QIT.Container.Base
open import Data.Product
open import Data.Sum
open import QIT.QW

data Sᵀ : Set where
  l : Sᵀ
  n : Sᵀ

Pᵀ : Sᵀ → Set
Pᵀ l = ⊥*
Pᵀ n = I

T = W Sᵀ Pᵀ

Fᵀ : Set → Set
Fᵀ X = Σ Sᵀ λ s → Pᵀ s → X

leaf≡leaf : ∀ (f g : ⊥* → T) → sup (l , f) ≡ sup (l , g)
leaf≡leaf f g =
  ≡.cong (λ ○ → sup (l , ○)) (funExt λ ())

_∘ᵗ_ : ∀ (α : I → T) (π : I ↔ I)
     → I → T
(f ∘ᵗ π) = λ i → f (π .↔.to i)

sig : QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
sig = record
  { S = Sᵀ
  ; P = Pᵀ
  ; E = I ↔ I
  ; Ξ = λ π → record
    { V = I
    ; lhs = sup (inj₂ n , λ i → sup (inj₁ i , λ()))
    ; rhs = sup (inj₂ n , λ i → sup (inj₁ (π .↔.to i) , λ())) } }
