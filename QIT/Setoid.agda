-- Setoids and categorical structures based on equivalence relations.
--
-- This module provides the categorical foundations for working with quotient
-- structures in type theory. Instead of using propositional equality, we work
-- with setoids - sets equipped with user-defined equivalence relations.
--
-- Key components:
--
-- **Basic setoid theory:**
-- - Setoids: carriers with equivalence relations and proofs
-- - Homomorphisms: functions preserving equivalence relations
-- - Isomorphisms: bijective homomorphisms with explicit inverses
--
-- **Categorical structures:**
-- - Functors: structure-preserving maps between setoid categories
-- - Algebras: setoids with operations satisfying equational laws
-- - Diagrams: functors from preorders to setoids (moved from QIT.QW)
--
-- **Applications:**
-- - Quotient types: represent equivalence classes explicitly
-- - Extensional equality: functions equal when they produce equivalent outputs
-- - Algebraic structures: groups, rings, etc. with proper quotients
--
-- This provides the mathematical machinery needed to implement quotient
-- inductive types as colimits of diagrams, where the equivalence relations
-- enforce the desired equations at each stage of construction.
--
-- The module is organized with a submodule ≈ containing all definitions,
-- then selectively re-exports the most commonly used items.

module QIT.Setoid where

module ≈ where
  open import QIT.Setoid.Base public
  open import QIT.Setoid.Hom public
  open import QIT.Setoid.Iso public
  open import QIT.Setoid.Functor public
  open import QIT.Setoid.Algebra public
  open import QIT.Setoid.Diagram public

open ≈ using (Setoid; ⟨_⟩; _/≡; _≈h_; _[_≈_]; _≅_; ≡p→≈; ≡→≈) public
