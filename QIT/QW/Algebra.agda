open import QIT.Prelude
open import QIT.Setoid
open import QIT.Container.Base
open import QIT.QW.Equation using (Equation)
open import QIT.QW.Signature

-- Define algebras that satisfy the equations of a QIT signature.
-- These are container algebras equipped with proofs that they satisfy
-- all equations in the signature. The initial such algebra gives the
-- quotient inductive type itself.
module QIT.QW.Algebra {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where

open Sig sig
open import QIT.Container.Functor S P (ℓS ⊔ ℓP ⊔ ℓV) (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.QW.Equation S P ℓV

-- A QIT algebra: a container algebra that satisfies the signature equations.
-- This consists of a setoid with operations (container algebra) plus
-- proofs that all equations hold in this algebra.
record Alg : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ lsuc ℓV) where
  field
    -- Underlying container algebra: setoid + structure map
    alg : ≈.Algebra F
    -- Satisfaction: all equations in the signature hold
    sat : Sat alg Ξ
  open ≈.Algebra alg public

-- Homomorphism between QIT algebras: just container algebra homomorphisms.
-- The satisfaction proofs are automatically preserved by homomorphisms,
-- so we only need to give the underlying algebra homomorphism.
record Hom (Xα Yβ : Alg) : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ lsuc ℓV) where
  field
    hom : ≈.Alg.Hom F (Alg.alg Xα) (Alg.alg Yβ)

  -- Re-export the underlying homomorphism for convenience
  open ≈.Alg.Hom hom renaming (hom to alghom) public

-- Initial QIT algebra: has a unique homomorphism to every other QIT algebra.
-- This characterizes the "free" or "syntax" algebra where only the signature
-- equations hold and no additional equations are imposed.
record IsInitial (Xα : Alg) : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ lsuc ℓV) where
  open Hom
  field
    -- Recursor: canonical map to any QIT algebra
    rec : ∀ Yβ → Hom Xα Yβ
    -- Uniqueness: any homomorphism equals the recursor
    unique : ∀ Yβ (f : Hom Xα Yβ) → f .alghom ≈h (rec Yβ) .alghom

-- Package of initial QIT algebra: the algebra together with initiality proof.
-- This represents the quotient inductive type defined by the signature.
record Record : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ lsuc ℓV) where
  field
    -- The initial algebra
    Xα : Alg
    -- Proof that it's initial
    initial : IsInitial Xα
