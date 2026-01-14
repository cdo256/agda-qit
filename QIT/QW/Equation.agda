open import QIT.Prelude

-- Define expressions and equations over container signatures.
-- Expressions are terms built from variables and constructors, used to
-- state equations that should hold in the quotient. This provides the
-- equational theory component of quotient inductive type signatures.
module QIT.QW.Equation {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Container.Base
open import QIT.Container.Functor S P
open import QIT.Setoid

-- Expressions over variables V: terms built from V and constructor signature (S,P).
-- These are W-types over the extended signature (V ⊎ S, Pʰ) where:
-- - Variables V have no arguments (arity ⊥*)
-- - Constructors S keep their original arities P
Expr : ∀ {ℓV} (V : Set ℓV) → Set (ℓS ⊔ ℓP ⊔ ℓV)
Expr {ℓV} V = W Sʰ Pʰ
  where
  -- Extended shapes: variables or constructors
  Sʰ : Set (ℓS ⊔ ℓV)
  Sʰ = V ⊎ S

  -- Extended positions: variables are nullary, constructors keep original arity
  Pʰ : Sʰ → Set ℓP
  Pʰ = ⊎.[ (λ _ → ⊥*) , P ]

pattern varᴱ v {f} = sup (inj₁ v , f)
pattern supᴱ s f = sup (inj₂ s , f)

-- An equation equates two expressions over the same set of variables.
-- This is the basic unit of equational specification: lhs ≈ rhs.
record Equation ℓV : Set (lsuc ℓV ⊔ ℓS ⊔ ℓP) where
  field
    -- Variables appearing in the equation
    V : Set ℓV
    -- Left-hand side expression
    lhs : Expr V
    -- Right-hand side expression
    rhs : Expr V


-- Equation satisfaction in a given algebra.
-- An algebra satisfies an equation if the lhs and rhs evaluate to
-- equivalent elements under all variable assignments.
module _ (Xα : ≈.Algebra (F (ℓS ⊔ ℓP) (ℓS ⊔ ℓP))) where
  open ≈.Algebra Xα
  module X = Setoid X

  -- Evaluate an expression in the algebra given a variable assignment.
  -- Variables are replaced by their assignments, constructors are interpreted
  -- using the algebra's structure map.
  assign : ∀ {ℓV} → {V : Set ℓV} (ϕ : V → ⟨ X ⟩) (e : Expr V) → ⟨ X ⟩
  assign ϕ (varᴱ v) = ϕ v
  assign ϕ (supᴱ s f) = α.to (s , λ i → assign ϕ (f i))
    where module α = ≈.Hom α

  -- Variable assignment for an equation: maps variables to algebra elements
  Assignment : ∀ {ℓV} → Equation ℓV → Set (ℓS ⊔ ℓP ⊔ ℓV)
  Assignment e = V → ⟨ X ⟩
    where open Equation e

  -- An equation is satisfied if lhs ≈ rhs under all variable assignments.
  -- This is universal quantification over all ways to instantiate variables.
  SatEq : ∀ {ℓV} → Equation ℓV
        → Prop (ℓS ⊔ ℓP ⊔ ℓV)
  SatEq e = ∀ (ϕ : Assignment e) → assign ϕ lhs X.≈ assign ϕ rhs
    where open Equation e

  -- Satisfaction of a collection of equations indexed by E.
  -- The algebra must satisfy every equation in the collection.
  Sat : ∀ {ℓE ℓV} → {E : Set ℓE}
      → (E → Equation ℓV)
      → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
  Sat Ξ = ∀ e → SatEq (Ξ e)
