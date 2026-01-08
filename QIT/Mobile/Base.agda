module QIT.Mobile.Base (I : Set) where

open import QIT.Prelude
open import QIT.Container.Base
open import Data.Product

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
(f ∘ᵗ π) = λ b → f (π .↔.to b)
