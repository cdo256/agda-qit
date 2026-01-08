{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.QW.Equation {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import Data.Sum
open import Data.Empty
open import Data.Product hiding (∃)
open import QIT.Container.Base
open import QIT.Container.Functor S P
open import QIT.Relation.Subset
open import QIT.Setoid

private
  T = W S P

Expr : ∀ {ℓV} (V : Set ℓV) → Set (ℓS ⊔ ℓP ⊔ ℓV)
Expr {ℓV} V = W Sʰ Pʰ
  where
  Sʰ : Set (ℓS ⊔ ℓV)
  Sʰ = V ⊎ S
  Pʰ : Sʰ → Set ℓP
  Pʰ = [ (λ _ → ⊥*) , P ]

module _ {ℓV} {V : Set ℓV} where
  data EqPath : (e : Expr V) → Set (ℓS ⊔ ℓP ⊔ ℓV) where
    epleaf : ∀ e → EqPath e
    epstep : ∀ s f i → EqPath (f i) → EqPath (sup (inj₂ s , f))

  ⟦_⟧ᴱᴾ : {e : Expr V} (p : EqPath e) → Expr V
  ⟦ epleaf e ⟧ᴱᴾ = e
  ⟦ epstep s f i p ⟧ᴱᴾ = ⟦ p ⟧ᴱᴾ

  _[_] : (V → T) → Expr V → T
  ϕ [ (sup (inj₁ v , _)) ] = ϕ v
  ϕ [ (sup (inj₂ s , f)) ] = sup (s , λ i → ϕ [ f i ])

record Equation ℓV : Set (lsuc ℓV ⊔ ℓS ⊔ ℓP) where
  field
    V : Set ℓV
    lhs : Expr V
    rhs : Expr V

module _ {ℓX ℓ≈} (Xα : ≈.Algebra (F ℓX ℓ≈)) where
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
      → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV ⊔ ℓ≈)
  Sat Ξ = ∀ e → SatEq (Ξ e)
