open import QIT.Prelude
open import QIT.QW

module QIT.Stage.Homo2 {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Relation.Binary
open import QIT.Container
open import QIT.Setoid as ≈
open import Data.Product hiding (∃)
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Subset
open import QIT.Relation.Plump S P
open import QIT.Diagram ≤p
open import QIT.Stage.Base S P
open import Data.Maybe
open import QIT.SystemOfEquations S P

private
  T = W S P
  variable
    ℓE ℓV ℓ≈ ℓE' ℓV' ℓ≈' : Level

ιᴱ : {V : Set ℓV} → Expr V → Z
ιᴱ (sup (inj₁ v , f)) = ⊥ᶻ
ιᴱ (sup (inj₂ s , f)) = sup (ιˢ s , λ i → ιᴱ (f i))

_≤ᴱ_ : {V : Set ℓV} → Expr V → Z → Prop (ℓS ⊔ ℓP)
t ≤ᴱ α = ιᴱ t ≤ α

record Assignᵇ {V : Set ℓV} (α : Z) : Set (ℓS ⊔ ℓP ⊔ ℓV) where
  field
    ev : ∀ β → β ≤ α → V → P₀ β
    consistent : ∀ β γ → (β≤α : β ≤ α) (γ≤β : γ ≤ β) → (v : V)
                → ev β β≤α v ≡ pweaken γ≤β (ev γ (≤≤ β≤α γ≤β) v) 

Exprᵇ : {V : Set ℓV} → Z → Set (ℓS ⊔ ℓP ⊔ ℓV)
Exprᵇ {V = V} α = ΣP (Expr V) (_≤ᴱ α)

module _ (α : Z) (_≈_ : P₀ α → P₀ α → Prop ℓ≈) where
  SatEqᵇ : (e : Equation ℓV)
        → Prop (ℓS ⊔ ℓP ⊔ ℓV ⊔ ℓ≈)
  SatEqᵇ e =
    ∀ (ϕ : V → T) →
      (l≤α : assign ϕ lhs ≤ᵀ α) →
      (r≤α : assign ϕ rhs ≤ᵀ α) →
      (assign ϕ lhs , l≤α) ≈ (assign ϕ rhs , r≤α)
    where open Equation e

  Satᵇ : (SysEq ℓE ℓV) → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV ⊔ ℓ≈)
  Satᵇ Ξ = ∀ e → SatEqᵇ (getEq e)
    where open SysEq Ξ

  mapExprV : ∀ {V : Set ℓV} {V' : Set ℓV'} (f : V → V')
           → Expr V → Expr V'
  mapExprV f (sup (inj₁ v , g)) = sup (inj₁ (f v) , λ i → mapExprV f (g i))
  mapExprV f (sup (inj₂ s , g)) = sup (inj₂ s , λ i → mapExprV f (g i))
  
  _∘expr_ : {V : Set ℓV} {V' : V → Set ℓV'}
          → (e1 : Expr V) (e2 : ∀ v → Expr (V' v))
          → Expr (Σ V V')
  _∘expr_ {V = V} {V'} (sup (inj₁ v , f)) e2 = mapExprV (v ,_) (e2 v)
  _∘expr_ {V = V} {V'} (sup (inj₂ s , f)) e2 = sup ((inj₂ s) , (λ i → f i ∘expr e2))
  
  _∘eq_ : (Ξ : Equation ℓV) (N : Ξ .Equation.V → Equation ℓV')
       → Equation _
  Ξ ∘eq N = record
    { V = Σ (Ξ .V) λ v → N v .V
    ; lhs = Ξ .lhs ∘expr λ v → N v .lhs
    ; rhs = Ξ .rhs ∘expr λ v → N v .rhs }
    where
    open Equation

  -- TODO: Prove composition preserves satisfaction.

module _ {ℓS ℓP ℓE ℓV} (qw : QW ℓS ℓP ℓE ℓV) where
  open QW qw
  data _⊢_≈ᵇ_ : (α : Z) → P₀ α → P₀ α → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV) where
    ≈pcong : ∀ a μ (f g : ∀ i → P₀ (μ i))
          → (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
          → sup (ιˢ a , μ) ⊢ psup a μ f ≈ᵇ psup a μ g
    ≈psat : ∀ {α} → {!!}
    ≈psym : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ ŝ
    ≈ptrans : ∀ {α ŝ t̂ û} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ û → α ⊢ ŝ ≈ᵇ û
    ≈pweaken : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : P₀ α}
            → α ⊢ ŝ ≈ᵇ t̂ → β ⊢ pweaken α≤β ŝ ≈ᵇ pweaken α≤β t̂

