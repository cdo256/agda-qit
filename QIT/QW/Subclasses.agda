open import QIT.Prelude
open import QIT.Prop
open import QIT.QW.Signature

module QIT.QW.Subclasses
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  where

open Sig sig

open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Algebra.Base F
open import QIT.Algebra.Lift S P

open import QIT.QW.W S P
open import QIT.QW.Equation S P ℓV
open import QIT.Plump.W S P
open import QIT.Plump.Properties Zᴬ as Z

module _ where
  expr→Z : {V : Set ℓV} → Expr V → Z
  expr→Z (varᴱ _) = ⊥ᶻ
  expr→Z (supᴱ s f) = supᶻ (s , λ i → expr→Z (f i))

  _≤ᴱ_ : {V : Set ℓV} → Expr V → Z → Prop (ℓS ⊔ ℓP)
  e ≤ᴱ α = expr→Z e ≤ α

  T-alg* : Algebra
  T-alg* = LiftAlgebra ℓV T-alg
  assignT : {V : Set ℓV} → (V → T) → Expr V → T
  assignT ρ e = lower (assign T-alg* (λ v → lift (ρ v)) e)
  
  record DepthPreservingSig
    : Prop (ℓE ⊔ ℓS ⊔ ℓP ⊔ ℓV) where
    open Equation
    field
      dpe : (e : E) (ρ : Ξ e .V  → T)
         →  ιᶻ (assignT ρ (Ξ e .lhs))
         ≤≥ ιᶻ (assignT ρ (Ξ e .rhs))

  LocalEquation : (E : Equation) → (α : Z) → Prop (ℓS ⊔ ℓP)
  LocalEquation E α = E.lhs ≤ᴱ α ∧ E.rhs ≤ᴱ α
    where
    module E = Equation E
