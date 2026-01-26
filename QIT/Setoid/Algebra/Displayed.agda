module QIT.Setoid.Algebra.Displayed where

open import QIT.Prelude hiding (subst; lift)
open import QIT.Setoid.Base
open import QIT.Setoid.Hom renaming (Hom to ≈Hom)
open import QIT.Setoid.Functor
open import QIT.Setoid.Algebra.Base

-- ----------------------------------------------------------------------
-- 1. Family (The Motive)
-- ----------------------------------------------------------------------
-- A Family is a "Setoid-valued predicate" over a base Setoid X.
-- It consists of a Setoid for every x : X, equipped with transport.
record Family {ℓX ℓX'} (X : Setoid ℓX ℓX') (ℓP ℓP' : Level) : Set (ℓX ⊔ ℓX' ⊔ lsuc ℓP ⊔ lsuc ℓP') where
  field
    P : ⟨ X ⟩ → Setoid ℓP ℓP'
    
    -- Transport: If base elements are equal, the fibers are compatible.
    -- (For strict uniqueness, we often need this to be an equivalence).
    subst : ∀ {x y} → X [ x ≈ y ] → ≈Hom (P x) (P y)

  subst₀ : ∀ {x y} → X [ x ≈ y ] → ⟨ P x ⟩ → ⟨ P y ⟩
  subst₀ p = subst p .≈Hom.to
    

-- ----------------------------------------------------------------------
-- 2. Lifting the Functor (Displayed Functor)
-- ----------------------------------------------------------------------
-- To define an algebra *on* a family, we must know how the functor F
-- transforms the family. 
--
-- If F is a Container (S, P), then for u : F X, an element of (LiftF u)
-- is a function mapping every position in the shape of u to an element 
-- of the family.
module _ {ℓX ℓX'} (F : Functor ℓX ℓX' ℓX ℓX') where
  open Functor F

  -- We assume F comes with a way to lift families. 
  -- (In a full library, this is part of the Container/Functor spec).
  record FunctorLifting : Set (lsuc ℓX ⊔ lsuc ℓX') where
    field
      lift : ∀ {X : Setoid ℓX ℓX'} → 
             Family X ℓX ℓX' →    -- Given a family P over X
             Family (F-ob X) ℓX ℓX' -- We get a family over F X

-- ----------------------------------------------------------------------
-- 3. Displayed Algebra (The Inductive Step)
-- ----------------------------------------------------------------------
module _ {ℓX ℓX'} (F : Functor ℓX ℓX' ℓX ℓX') (Lift : FunctorLifting F) where
  open Functor F
  open FunctorLifting Lift

  -- A Displayed Algebra consists of a base algebra (X, α) and a method
  -- for transforming "proofs of the arguments" into "proofs of the result".
  record DisplayedAlgebra (Alg : Algebra F) 
                          (Fam : Family (Algebra.X Alg) ℓX ℓX') 
                          : Set (lsuc ℓX ⊔ lsuc ℓX') where
    open Family Fam
    open Algebra Alg renaming (sup to sup')
    
    -- F̂ P
    private
      module P = Family Fam
      F̂P = lift Fam 
      FP = Family.P F̂P
      module F̂P = Family F̂P

    field
      -- The Dependent Methods.
      -- Roughly: ∀ (u : F X), F̂P(u) → P(α u)
      -- This must be a homomorphism in the "Total Category" of families.
      method : ∀ {u : ⟨ F-ob X ⟩}
             → ≈Hom (FP u) (P (sup' u))

-- ----------------------------------------------------------------------
-- 4. Application: Proving Uniqueness
-- ----------------------------------------------------------------------
-- To prove that an algebra X is initial, we need the "Induction Principle":
-- For any Displayed Algebra, there exists a section.

  record IsInductive (Xα : Algebra F) : Set (lsuc ℓX ⊔ lsuc ℓX') where
    open Algebra Xα
    field
      ind : ∀ {Fam : Family X ℓX ℓX'} →
            (D : DisplayedAlgebra Xα Fam) →
            -- The result is a dependent function (section)
            ∀ (x : ⟨ X ⟩) → ⟨ Family.P Fam x ⟩

  -- STRATEGY FOR UNIQUENESS:
  -- 1. Given two homomorphisms f, g : Hom X Y
  -- 2. Define the Family 'EqFam' where EqFam.P x = (f x ≈ g x)
  -- 3. Define the Displayed Algebra structure on EqFam:
  --    This involves showing that if arguments are equal (f a ≈ g a), 
  --    then the results are equal (f (α (sup a)) ≈ g (α (sup a))).
  --    This holds because f and g are homomorphisms.
  -- 4. Apply 'ind' to get ∀ x, f x ≈ g x.
