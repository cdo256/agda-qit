open import QIT.Prelude

module QIT.SystemOfEquations {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

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

_[_] : ∀ {ℓV} {V : Set ℓV} → (V → T) → Expr V → T
ϕ [ (sup (inj₁ v , _)) ] = ϕ v
ϕ [ (sup (inj₂ s , f)) ] = sup (s , λ i → ϕ [ f i ])

record SysEq ℓE ℓV : Set (lsuc ℓE ⊔ lsuc ℓV ⊔ ℓS ⊔ ℓP) where
  field
    E : Set ℓE
    V : E → Set ℓV
    lhs : (e : E) → Expr (V e)
    rhs : (e : E) → Expr (V e)

module _ {ℓE ℓV} (Ξ : SysEq ℓE ℓV) where
  open SysEq Ξ
  data ⟦_⟧[_≈_] : T → T → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV) where
    ≈ξrefl : ∀ {x} → ⟦_⟧[_≈_] x x
    ≈ξsym : ∀ {x y} → ⟦_⟧[_≈_] x y → ⟦_⟧[_≈_] y x
    ≈ξtrans : ∀ {x y z} → ⟦_⟧[_≈_] x y → ⟦_⟧[_≈_] y z → ⟦_⟧[_≈_] x z
    ≈ξeq : ∀ e (ϕ : V e → T) → ⟦_⟧[_≈_] (ϕ [ lhs e ]) (ϕ [ rhs e ])
    --TODO: Should we omit ≈ξcong?
    ≈ξcong : ∀ s (f g : P s → T) → (∀ i → ⟦_⟧[_≈_] (f i) (g i))
           → ⟦_⟧[_≈_] (sup (s , f)) (sup (s , g))
