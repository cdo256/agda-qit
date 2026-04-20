open import QIT.Prelude
open import QIT.Prop

-- Define expressions and equations over container signatures.
-- Expressions are terms built from variables and constructors, used to
-- state equations that should hold in the quotient. This provides the
-- equational theory component of quotient inductive type signatures.
module QIT.QW.Equation {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓV : Level) where

open import QIT.Container.Base
open import QIT.Container.Properties
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Setoid
open import QIT.QW.W S P
open import QIT.Functor.Base

module Fᴱ = Functor F

open import QIT.Algebra.Base F as Alg

-- Expressions over variables V: terms built from V and constructor signature (S,P).
-- These are W-types over the extended signature (V ⊎ S, Pʰ) where:
-- - Variables V have no arguments (arity ⊥*)
-- - Constructors S keep their original arities P
-- Extended shapes: variables or constructors
Sʰ : (V : Set ℓV) → Set (ℓS ⊔ ℓV)
Sʰ V = V ⊎ S

-- Extended positions: variables are nullary, constructors keep original arity
Pʰ : (V : Set ℓV) → Sʰ V → Set ℓP
Pʰ V = ⊎.[ (λ _ → ⊥*) , P ]

Expr : (V : Set ℓV) → Set (ℓS ⊔ ℓP ⊔ ℓV)
Expr V = W (Sʰ V) (Pʰ V)
-- Expr V = FreeAlgebra S P V

pattern varᴱ v {f} = sup (inj₁ v , f)
pattern supᴱ s f = sup (inj₂ s , f)

ιᴱ : {V : Set ℓV} → W S P → Expr V
ιᴱ (sup (s , f)) = supᴱ s λ i → ιᴱ (f i)

ExprAlg : (V : Set ℓV) → Algebra
ExprAlg V = record
  { X = Expr V
  ; α = β }
  where
  β : ⟦ S ◁ P ⟧ (Expr V) → Expr V
  β (s , f) = supᴱ s f

-- An equation equates two expressions over the same set of variables.
-- This is the basic unit of equational specification: lhs ≈ rhs.
record Equation : Set (lsuc ℓV ⊔ ℓS ⊔ ℓP) where
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
module _ (Xα : Algebra) where
  open Algebra Xα

  -- Evaluate an expression in the algebra given a variable assignment.
  -- Variables are replaced by their assignments, constructors are interpreted
  -- using the algebra's structure map.
  assign : {V : Set ℓV} (ϕ : V → X) (e : Expr V) → X
  assign ϕ = recW ⊎.[ (λ v _ → ϕ v) , (λ s f → α (s , f)) ]

  -- Variable assignment for an equation: maps variables to algebra elements
  Assignment : Equation → Set (ℓS ⊔ ℓP ⊔ ℓV)
  Assignment e = V → X
    where open Equation e

  -- An equation is satisfied if lhs ≈ rhs under all variable assignments.
  -- This is universal quantification over all ways to instantiate variables.
  SatEq : Equation → Prop (ℓS ⊔ ℓP ⊔ ℓV)
  SatEq e = ∀ (ϕ : Assignment e) → assign ϕ lhs ≡ assign ϕ rhs
    where open Equation e

  -- Satisfaction of a collection of equations indexed by E.
  -- The algebra must satisfy every equation in the collection.
  Sat : ∀ {ℓE} → {E : Set ℓE}
      → (E → Equation)
      → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
  Sat Ξ = ∀ e → SatEq (Ξ e)

module _ {V : Set ℓV} {Xα : Algebra}
         (h : Hom (ExprAlg V) Xα) where
  open Hom h
  open Algebra Xα
  open ≡

  assign-unique
    : (ρ : V → X)
    → (vsat : ∀ v f → hom (varᴱ v {f}) ≡ ρ v)
    → (e : Expr V)
    → hom e ≡ assign Xα ρ e
  assign-unique ρ vsat (varᴱ v {f}) = begin
    hom (varᴱ v {f})
      ≡⟨ vsat v f ⟩
    ρ v
      ≡⟨ refl ⟩
    assign Xα ρ (varᴱ v {f}) ∎
    where
    open ≡.≡-Reasoning
  assign-unique ρ vsat (supᴱ s f) = begin
    hom (supᴱ s f)
      ≡⟨ sym (comm {s , f}) ⟩
    α (Fᴱ.hom hom (s , f))
      ≡⟨ cong (λ ○ → α (s , ○)) (funExt λ x → assign-unique ρ vsat (f x)) ⟩
    α (s , (λ i → assign Xα ρ (f i)))
      ≡⟨ refl ⟩
    assign Xα ρ (supᴱ s f) ∎
    where
    open ≡-Reasoning
    q : (x : P s) → hom (f x) ≡ assign Xα ρ (f x)
    q x =
      hom (f x)
        ≡⟨ assign-unique ρ vsat (f x) ⟩
      assign Xα ρ (f x) ∎
