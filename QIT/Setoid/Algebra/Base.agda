{-# OPTIONS --allow-unsolved-metas #-}
open import QIT.Prelude

-- Define algebras over setoid endofunctors. An algebra for a functor F
-- is a setoid X equipped with a structure map α : F X → X. This is the
-- foundation for defining initial algebras and recursive data types.
module QIT.Setoid.Algebra.Base where

open import QIT.Setoid.Base
open import QIT.Setoid.Hom renaming (Hom to ≈Hom)
open import QIT.Setoid.Functor
open import QIT.Container.Base hiding (sup)

-- Define an algebra over a setoid endofunctor.
-- This is just a setoid X paired with a homomorphism:
--    α : F X → X
-- This is used for defining initial algebras.
module _ {ℓX ℓX'} (F : Functor ℓX ℓX' ℓX ℓX') where
  open Functor F

  SupType : (X : Setoid ℓX ℓX') → Set (ℓX ⊔ ℓX')
  SupType X = ≈Hom (F-ob X) X 

  -- An F-algebra consists of a setoid carrier X and a structure map α : F X → X.
  -- The structure map gives meaning to the functor's operations on the carrier.
  -- For example, if F represents tree operations, α tells us how to build trees.
  record Algebra : Set (lsuc ℓX ⊔ lsuc ℓX') where
    constructor mkAlg
    field
      -- The carrier setoid
      X : Setoid ℓX ℓX'
      -- Structure map: interprets F-structure as elements of X
      α : SupType X

    -- Convenient accessor for the underlying function
    sup = α .≈Hom.to

  -- Homomorphism between F-algebras: a homomorphism of carriers that
  -- commutes with the structure maps. If f : X → Y is an algebra homomorphism,
  -- then f(α(fx)) = β(F(f)(fx)) for all fx : F X.
  record Hom (Xα Yβ : Algebra) : Set (lsuc ℓX ⊔ lsuc ℓX') where
    constructor mkHom
    open Algebra Xα
    open Algebra Yβ renaming (X to Y; α to β)
    field
      -- Underlying homomorphism between carriers
      hom : ≈Hom X Y
      -- Commutativity condition: the square commutes
      comm : (β ∘ F-mor hom) ≈h (hom ∘ α)
    open ≈Hom hom public

  -- An initial algebra has a unique homomorphism to every other algebra.
  -- This property characterizes recursive data types: the initial algebra
  -- gives the "freely generated" elements with no additional equations.
  record IsInitial (Xα : Algebra) : Set (lsuc ℓX ⊔ lsuc ℓX') where
    constructor mkIsInitial
    open Algebra Xα
    open Hom
    field
      -- Recursor: unique map to any algebra
      rec : ∀ Yβ → Hom Xα Yβ
      -- Uniqueness: any algebra homomorphism equals the recursor
      unique : ∀ Yβ → (f : Hom Xα Yβ) → f .hom ≈h rec Yβ .hom
      
module _
  {ℓX ℓX' : Level}                              -- The original algebra levels
  (ℓl ℓl' : Level)                              -- The lifting levels
  (F : Functor ℓX ℓX' ℓX ℓX') 
  where

  -- -- Import the Functor at both level configurations
  -- import QIT.Container.Functor S P ℓX ℓX' as FSmall
  -- import QIT.Container.Functor S P (ℓX ⊔ ℓl) (ℓX' ⊔ ℓl') as FBig

  -- -- Import the Algebra definitions for both functors
  -- import QIT.Setoid.Algebra.Alg FSmall.F as AlgSmall
  -- import QIT.Setoid.Algebra.Alg FBig.F as AlgBig

  -- Helper to strip the LiftP wrapper from the input equality
  lowerP : ∀ {ℓ a} {A : Prop a} → LiftP ℓ A → A
  lowerP (liftp p) = p

  -- liftAlgebra : Algebra F → Algebra {!!}
  -- liftAlgebra alg = AlgBig.mkAlg X-lifted α-lifted
  --   where
  --     open AlgSmall.Algebra alg renaming (X to X-small; α to α-small)

  --     -- 1. Lift the Carrier Setoid
  --     X-lifted : Setoid (ℓX ⊔ ℓl) (ℓX' ⊔ ℓl')
  --     X-lifted = LiftSetoid ℓl ℓl' X-small

  --     -- 2. Define the structure map components

  --     -- The underlying function: (S × (P s → Lift X)) → Lift X
  --     -- Note: FBig.F-ob carrier is typically Σ S (λ s → P s → Carrier X-lifted)
  --     op : Carrier (FBig.F.F-ob X-lifted) → Carrier X-lifted
  --     op (s , k) = lift (α-small .to (s , λ p → lower (k p)))

  --     -- The congruence proof
  --     -- We must show that if (s, k) ≈ (s', k'), then op(s, k) ≈ op(s', k')
  --     cong : {x y : Carrier (FBig.F.F-ob X-lifted)} → 
  --            x FBig.F.≈F y → 
  --            Setoid._≈_ X-lifted (op x) (op y)
  --     cong {s , k} {s' , k'} (eqS , eqK) = 
  --       -- Result must be in LiftP
  --       liftp (α-small .cong (eqS , lower-eqK))
  --       where
  --         -- Convert the high-level pointwise equality to low-level
  --         lower-eqK : ∀ p → Setoid._≈_ X-small (lower (k p)) (lower (k' (subst P eqS p)))
  --         lower-eqK p = lowerP (eqK p)

  --     -- 3. Assemble the Homomorphism
  --     α-lifted : ≈Hom (FBig.F.F-ob X-lifted) X-lifted
  --     α-lifted = record 
  --       { to   = op 
  --       ; cong = cong 
  --       }
