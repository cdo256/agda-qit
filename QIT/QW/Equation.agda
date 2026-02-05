open import QIT.Prelude

-- Define expressions and equations over container signatures.
-- Expressions are terms built from variables and constructors, used to
-- state equations that should hold in the quotient. This provides the
-- equational theory component of quotient inductive type signatures.
module QIT.QW.Equation {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓV : Level) where

open import QIT.Container.Base
open import QIT.Container.Functor S P (ℓS ⊔ ℓP ⊔ ℓV) (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Setoid
open import QIT.QW.W S P

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

ExprAlg : (V : Set ℓV) → ≈.Algebra F
ExprAlg V = record
  { X = Expr V /≡
  ; α = record
    { to = β 
    ; cong = β-cong } }
  where
  Ẽ : Setoid _ _
  Ẽ = Expr V /≡
  open F-Ob Ẽ
  β : ⟦ S ◁ P ⟧ (Expr V) → Expr V
  β (s , f) = supᴱ s f
  β-cong : ∀ {sf tg} → (p : sf ≈ꟳ tg) → (β sf ≡p β tg)
  β-cong {s , f} {s , g} (mk≈ꟳ ≡.refl snd≈) = congp (λ ○ → β (s , ○)) f≡g
    where
    f≡g : f ≡p g
    f≡g = funExtp snd≈

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
module _ (Xα : ≈.Algebra F) where
  open ≈.Algebra Xα
  module X = Setoid X

  -- Evaluate an expression in the algebra given a variable assignment.
  -- Variables are replaced by their assignments, constructors are interpreted
  -- using the algebra's structure map.
  assign : {V : Set ℓV} (ϕ : V → ⟨ X ⟩) (e : Expr V) → ⟨ X ⟩
  assign ϕ = recW ⊎.[ (λ v _ → ϕ v) , (λ s f → α.to (s , f)) ]
    where module α = ≈.Hom α

  -- Variable assignment for an equation: maps variables to algebra elements
  Assignment : Equation → Set (ℓS ⊔ ℓP ⊔ ℓV)
  Assignment e = V → ⟨ X ⟩
    where open Equation e

  -- An equation is satisfied if lhs ≈ rhs under all variable assignments.
  -- This is universal quantification over all ways to instantiate variables.
  SatEq : Equation → Prop (ℓS ⊔ ℓP ⊔ ℓV)
  SatEq e = ∀ (ϕ : Assignment e) → assign ϕ lhs X.≈ assign ϕ rhs
    where open Equation e

  -- Satisfaction of a collection of equations indexed by E.
  -- The algebra must satisfy every equation in the collection.
  Sat : ∀ {ℓE} → {E : Set ℓE}
      → (E → Equation)
      → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
  Sat Ξ = ∀ e → SatEq (Ξ e)

module _ {V : Set ℓV} {Xα : ≈.Algebra F}
         (h : ≈.Alg.Hom F (ExprAlg V) Xα) where
  module h = ≈.Alg.Hom h
  open ≈.Algebra Xα
  open Setoid X
  module α = ≈.Hom α

  assign-unique
    : (ρ : V → ⟨ X ⟩)
    → (vsat : ∀ v f → X [ h.to (varᴱ v {f}) ≈ ρ v ])
    → (e : Expr V)
    → X [ h.to e ≈ assign Xα ρ e ]
  assign-unique ρ vsat (varᴱ v {f}) = begin
    h.to (varᴱ v {f})
      ≈⟨ vsat v f ⟩
    ρ v
      ≈⟨ refl ⟩
    assign Xα ρ (varᴱ v {f}) ∎
    where
    open ≈.≈syntax {S = X}
  assign-unique ρ vsat (supᴱ s f) = begin
    h.to (supᴱ s f)
      ≈⟨ sym h.comm ⟩
    α.to (Fh (s , f))
      ≈⟨ α.cong (F-Ob.mk≈ꟳ ≡.refl λ i → refl) ⟩
    α.to (s , λ i → h.to (f i))
      ≈⟨ α.cong (F-Ob.mk≈ꟳ ≡.refl λ i → assign-unique ρ vsat (f i)) ⟩
    α.to (s , (λ i → assign Xα ρ (f i)))
      ≈⟨ refl ⟩
    assign Xα ρ (supᴱ s f) ∎
    where
    module F = ≈.Functor F
    F₀ : Setoid (ℓS ⊔ ℓP ⊔ ℓV) (ℓS ⊔ ℓP ⊔ ℓV)
       → Setoid (ℓS ⊔ ℓP ⊔ ℓV) (ℓS ⊔ ℓP ⊔ ℓV)
    F₀ = F.F-ob
    Fh : ⟨ F₀ (Expr V /≡) ⟩ → ⟨ F₀ X ⟩
    Fh = ≈.Hom.to (F.F-hom h.hom) 
    open ≈.≈syntax {S = X}
