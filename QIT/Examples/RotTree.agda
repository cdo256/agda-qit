module QIT.Examples.RotTree (A : Set) where

-- Binary trees with rotation equation demonstrating a quotient inductive type
-- that implements associativity of branching. This serves as a canonical example
-- of how QITs can encode algebraic structures with non-trivial equational theories.

open import QIT.Prelude
open import QIT.Container.Base
open import QIT.QW
open import Data.Nat
open import Data.Fin
open import Data.Vec

-- Shape type: describes the form of tree nodes.
-- Leaves hold data elements of type A, branches have exactly two children.
data Sᵀ : Set where
  l : A → Sᵀ    -- Leaf constructor parameterized by data
  n : Sᵀ        -- Branch/node constructor (binary)

-- Position function: specifies how many children each shape has.
-- Leaves have no children, branches have exactly 2 children.
Pᵀ : Sᵀ → Set
Pᵀ (l x) = ⊥     -- Leaves have no positions/children
Pᵀ n = Fin 2     -- Branches have 2 positions (left=0, right=1)

-- The underlying W-type of raw trees before quotienting.
T = W Sᵀ Pᵀ

-- Smart constructor for building branch expressions.
-- Takes two sub-expressions and combines them into a branch node.
branchᴱ : ∀ {V : Set} (s t : QW.Expr Sᵀ Pᵀ ℓ0 V) → QW.Expr Sᵀ Pᵀ ℓ0 V
branchᴱ s t = QW.supᴱ n (lookup (s ∷ t ∷ []))

-- Variable constructor for equation building.
var : ∀ {V : Set} (v : V) → QW.Expr Sᵀ Pᵀ ℓ0 V
var v = QW.varᴱ v {λ()}

-- The rotation equation: associativity of branching.
-- branch(s, branch(t, u)) ≡ branch(branch(s, t), u)
-- This makes branching associative, similar to (a + b) + c = a + (b + c).
rot : QW.Equation Sᵀ Pᵀ ℓ0
rot = record
  { V = Fin 3                           -- Three variables: s, t, u
  ; lhs = branchᴱ sⱽ (branchᴱ tⱽ uⱽ)    -- Left-hand side: s(t u)
  ; rhs = branchᴱ (branchᴱ sⱽ tⱽ) uⱽ    -- Right-hand side: (s t)u
  }
  where
  sⱽ = var zero              -- s = variable 0
  tⱽ = var (suc zero)        -- t = variable 1
  uⱽ = var (suc (suc zero))  -- u = variable 2

-- The complete signature for rotation trees as a QIT.
-- Packages the container signature with the rotation equation.
RotTree : QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
RotTree = record
  { S = Sᵀ           -- Shape constructors
  ; P = Pᵀ           -- Position functions
  ; E = ⊤            -- Equation names (just one: rotation)
  ; Ξ = λ _ → rot    -- Equation interpretation
  }
