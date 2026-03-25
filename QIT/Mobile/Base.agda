-- Permutation invariant trees: An example of quotient inductive types.
--
-- This module defines "mobiles" - tree structures where the order of branches
-- doesn't matter. A mobile is an I-branching tree quotiented by permutations
-- of the branching structure. This demonstrates how QITs can capture algebraic
-- structures that are invariant under group actions.
--
-- The construction illustrates several key concepts:
-- - Container signatures for tree-like data structures
-- - Quotient equations that identify permuted variants
-- - How symmetries arise naturally in combinatorial structures
--
-- Mathematical interpretation:
-- A mobile represents a tree where each internal node has exactly I children,
-- but the labeling/ordering of these children is irrelevant. Two mobiles are
-- equivalent if one can be obtained from the other by permuting child indices.
-- Note that I can be any set (finite, countable, or uncountable).
--
-- This is useful for modeling:
-- - Unordered tree structures (syntax trees, decision trees)
-- - Combinatorial objects with inherent symmetries
-- - Data structures where permutation equivalence is natural
module QIT.Mobile.Base (I : Set) where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Container.Base
open import QIT.QW

-- Container signature for I-branching trees before quotienting.
-- We have two constructors: leaves (no children) and nodes (I children).
data Sᵀ : Set where
  l : Sᵀ  -- Leaf constructor
  n : Sᵀ  -- Node constructor

-- Arity function: leaves have no positions, nodes have I positions.
-- This gives us the standard I-ary tree structure.
Pᵀ : Sᵀ → Set
Pᵀ l = ⊥*  -- Leaves are nullary (no children)
Pᵀ n = I   -- Nodes have exactly I children

-- The underlying W-type: I-branching trees without quotient.
-- This gives us finite trees where each internal node branches I ways.
T = W Sᵀ Pᵀ

-- Container functor interpretation for the signature.
-- Maps a type X to the type of "one layer" of tree structure over X.
Fᵀ : Set → Set
Fᵀ X = Σ Sᵀ λ s → Pᵀ s → X

-- Technical lemma: leaf constructors are unique regardless of their
-- (impossible) children. This follows because ⊥* → T has a unique element.
leaf≡leaf : ∀ (f g : ⊥* → T) → sup (l , f) ≡ sup (l , g)
leaf≡leaf f g =
  ≡.cong (λ ○ → sup (l , ○)) (≡.funExt λ ())

-- Bijection action on I-indexed functions.
-- Given a function α : I → T and a bijection π : I ↔ I,
-- produce the function that applies π before α.
-- This is how bijections act on the children of nodes.
_∘ᵗ_ : ∀ (α : I → T) (π : I ↔ I)
     → I → T
(f ∘ᵗ π) = λ i → f (π .↔.to i)

-- The QIT signature for mobiles: trees quotiented by permutation invariance.
-- This signature captures the tree structure plus equations saying that
-- permuting the children of any node gives an equivalent tree.
-- The equations are indexed by all bijections I ↔ I (the symmetric group on I).
sig : QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
sig = record
  { S = Sᵀ                    -- Tree constructors (leaf, node)
  ; P = Pᵀ                    -- Arities (0, I)
  ; E = I ↔ I                 -- Equations indexed by bijections I ↔ I
  ; Ξ = λ π → record          -- Each bijection π gives an equation:
    { V = I                   --   Variables: one for each child position
    ; lhs = QW.supᴱ n (λ i → QW.varᴱ i {λ()})     -- n(xᵢ)ᵢ∈I
    ; rhs = QW.supᴱ n (λ i → QW.varᴱ (π .↔.to i) {λ()}) } } -- n(x_{π(i)})ᵢ∈I

-- The equations say: n(xᵢ)ᵢ∈I ≈ n(x_{π(i)})ᵢ∈I for any bijection π.
-- This makes node construction invariant under permutation of children,
-- giving us the "mobile" property where order doesn't matter.
--
-- In the expression language:
-- - inj₁ i represents variable i
-- - inj₂ n represents the node constructor
-- - sup builds expressions from constructors and arguments
--
-- The LHS builds n(xᵢ)ᵢ∈I and the RHS builds n(x_{π(i)})ᵢ∈I.
-- When these expressions are interpreted in any algebra satisfying the signature,
-- they must yield equivalent elements, enforcing permutation invariance.
--
-- Note: This works for any set I. The bijections I ↔ I form the symmetric
-- group on I, which captures all possible ways to reorder the I-indexed children.
