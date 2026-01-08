open import QIT.Prelude

module QIT.Equation {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import Data.Sum
open import Data.Empty
open import Data.Product hiding (∃)
open import QIT.Container
open import QIT.Relation.Subset

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

  record ExprMatch (e : Expr V) (t : T) : Set (ℓS ⊔ ℓP ⊔ ℓV) where
    field
      ϕ : V → T
      match : ϕ [ e ] ≡ t

record Equation ℓV : Set (lsuc ℓV ⊔ ℓS ⊔ ℓP) where
  field
    V : Set ℓV
    lhs : Expr V
    rhs : Expr V

record SysEq ℓE ℓV : Set (lsuc ℓE ⊔ lsuc ℓV ⊔ ℓS ⊔ ℓP) where
  field
    E : Set ℓE
    V : E → Set ℓV
    lhs : (e : E) → Expr (V e)
    rhs : (e : E) → Expr (V e)

  getEq : E → Equation ℓV
  getEq e = record
    { V = V e
    ; lhs = lhs e
    ; rhs = rhs e }

assign : ∀ {ℓV} → {V : Set ℓV} (ϕ : V → T) (e : Expr V) → T
assign ϕ (sup (inj₁ v , _)) = ϕ v
assign ϕ (sup (inj₂ s , f)) = sup (s , λ i → assign ϕ (f i))

SatEq : ∀ {ℓV ℓ≈} → Equation ℓV → (_≈_ : T → T → Prop ℓ≈)
      → Prop (ℓS ⊔ ℓP ⊔ ℓV ⊔ ℓ≈)
SatEq e _≈_ = ∀ (ϕ : V → T) → assign ϕ lhs ≈ assign ϕ rhs
  where open Equation e

Sat : ∀ {ℓE ℓV ℓ≈} → SysEq ℓE ℓV → (_≈_ : T → T → Prop ℓ≈)
    → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV ⊔ ℓ≈)
Sat Ξ _≈_ = ∀ e → SatEq (getEq e) _≈_
  where open SysEq Ξ
