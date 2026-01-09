open import QIT.Prelude

module QIT.QW.Equation {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Container.Base
open import QIT.Container.Functor S P
open import QIT.Setoid

Expr : ∀ {ℓV} (V : Set ℓV) → Set (ℓS ⊔ ℓP ⊔ ℓV)
Expr {ℓV} V = W Sʰ Pʰ
  where
  Sʰ : Set (ℓS ⊔ ℓV)
  Sʰ = V ⊎ S
  Pʰ : Sʰ → Set ℓP
  Pʰ = ⊎.[ (λ _ → ⊥*) , P ]

record Equation ℓV : Set (lsuc ℓV ⊔ ℓS ⊔ ℓP) where
  field
    V : Set ℓV
    lhs : Expr V
    rhs : Expr V

module _ (Xα : ≈.Algebra (F (ℓS ⊔ ℓP) (ℓS ⊔ ℓP))) where
  open ≈.Algebra Xα
  module X = Setoid X
  assign : ∀ {ℓV} → {V : Set ℓV} (ϕ : V → ⟨ X ⟩) (e : Expr V) → ⟨ X ⟩
  assign ϕ (sup (inj₁ v , _)) = ϕ v
  assign ϕ (sup (inj₂ s , f)) = α .≈.Hom.to (s , λ i → assign ϕ (f i))

  SatEq : ∀ {ℓV} → Equation ℓV
        → Prop (ℓS ⊔ ℓP ⊔ ℓV)
  SatEq e = ∀ (ϕ : V → ⟨ X ⟩) → assign ϕ lhs X.≈ assign ϕ rhs
    where open Equation e

  Sat : ∀ {ℓE ℓV} → {E : Set ℓE}
      → (E → Equation ℓV)
      → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
  Sat Ξ = ∀ e → SatEq (Ξ e)
