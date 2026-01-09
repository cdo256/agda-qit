-- Quotient W-types: The main construction for quotient inductive types (QITs).
--
-- This module implements quotient W-types as colimits of staged approximations.
-- A quotient W-type is specified by a signature containing both constructors
-- (via containers) and equations. The construction proceeds by:
--
-- 1. Building staged approximations indexed by plump ordinals
-- 2. Enforcing equations at each stage through a quotient relation
-- 3. Taking the colimit to obtain the final quotient type
-- 4. Proving this gives the initial algebra satisfying the equations
--
-- The key insight is that equations may require arbitrarily deep unfolding
-- of constructors, so we use plump ordinals to bound the "complexity" of
-- terms and build the quotient in stages of increasing complexity.
--
-- Mathematical foundation:
-- - Containers represent polynomial functors and their initial algebras (W-types)
-- - Equations specify additional constraints beyond the free algebra structure
-- - Plump ordinals provide size bounds for controlling infinite processes
-- - Colimits glue together all finite stages into the final quotient
--
-- The construction ensures that:
-- - All signature equations are satisfied in the final quotient
-- - The quotient has the universal property of initial algebras
-- - The process terminates due to well-foundedness of plump ordinals
--
-- This provides a systematic method for implementing QITs in type theory
-- without requiring them as primitives in the type system.

module QIT.QW where

module QW where
  open import QIT.QW.Equation public
  open import QIT.QW.Signature public
  open import QIT.QW.Algebra public
  open import QIT.QW.Colimit public
  open import QIT.QW.Cocontinuity public
