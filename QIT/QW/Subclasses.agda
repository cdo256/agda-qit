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

open import QIT.Nat using (ℕ)
import QIT.Container.Base as C
open import QIT.Container.Properties
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

  data ExprPath {V} (v : V) : Expr V → Set (ℓS ⊔ ℓP ⊔ ℓV) where
    here : ExprPath v (varᴱ v)
    there : ∀ s f i → ExprPath v (f i) → ExprPath v (supᴱ s f)

  ExprPathLength : ∀ {V} {v : V} → {e : Expr V} → ExprPath v e → ℕ
  ExprPathLength here = ℕ.zero
  ExprPathLength (there s f i p) = ℕ.suc (ExprPathLength p)

  record OccurrenceAtDepth {V : Set ℓV} (v : V) (e : Expr V) (n : ℕ)
    : Set (ℓS ⊔ ℓP ⊔ ℓV) where
    constructor atdepth
    field
      p : ExprPath v e
      len : ExprPathLength p ≡ n

  T-alg* : Algebra
  T-alg* = LiftAlgebra ℓV T-alg
  assignT : {V : Set ℓV} → (V → T) → Expr V → T
  assignT ρ e = lower (assign T-alg* (λ v → lift (ρ v)) e)


  occurence≤ : ∀ {V} → (e₁ e₂ : Expr V)
    → (∀ v n → OccurrenceAtDepth v e₁ n → OccurrenceAtDepth v e₂ n)
    → (∀ v n → OccurrenceAtDepth v e₂ n → OccurrenceAtDepth v e₁ n)
    → ∀ ρ → ιᶻ (assignT ρ e₁) ≤ ιᶻ (assignT ρ e₂)
  occurence≤ (varᴱ v₁) (varᴱ v₂) r l ρ with r v₁ 0 (atdepth here ≡.refl)
  ... | atdepth here _ = ≡→≤ (≡.cong ιᶻ (≡.cong ρ ≡.refl))
  occurence≤ (varᴱ v) (supᴱ s f) r l ρ with r v 0 (atdepth here ≡.refl)
  ... | atdepth (there s₁ f₁ i p) ()
  occurence≤ (supᴱ s f) (varᴱ v) r l ρ with l v 0 (atdepth here ≡.refl)
  ... | atdepth (there s₁ f₁ i p) ()
  occurence≤ (supᴱ s₁ f₁) (supᴱ s₂ f₂) r l ρ with r {!!} {!!} {!!}
  ... | u = sup≤ (λ i → <sup {!!} {!!})

{-
  record DepthPreservingSig
    : Set (ℓE ⊔ ℓS ⊔ ℓP ⊔ ℓV) where
    open Equation
    field
      dp→ : ∀ e v n
        → OccurrenceAtDepth v (Ξ e .lhs) n
        → OccurrenceAtDepth v (Ξ e .rhs) n
      dp← : ∀ e v n
        → OccurrenceAtDepth v (Ξ e .rhs) n
        → OccurrenceAtDepth v (Ξ e .lhs) n
    
    dpe : (e : E) (ρ : Ξ e .V  → T)
        →  ιᶻ (assignT ρ (Ξ e .lhs))
        ≤≥ ιᶻ (assignT ρ (Ξ e .rhs))
    dpe e ρ = ∧i
      occurence≤ (Ξ e .lhs) (Ξ e .rhs) (dp→ e) ρ ,
      occurence≤ (Ξ e .rhs) (Ξ e .lhs) (dp← e) ρ

  LocalEquation : (E : Equation) → (α : Z) → Prop (ℓS ⊔ ℓP)
  LocalEquation E α = E.lhs ≤ᴱ α ∧ E.rhs ≤ᴱ α
    where
    module E = Equation E
-}
