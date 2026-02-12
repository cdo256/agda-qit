open import QIT.Prelude
open import QIT.Prop

open import QIT.Category.Base
open import QIT.Functor.Base
open import QIT.Container.Base hiding (sup)

-- Define algebras over setoid endofunctors. An algebra for a functor F
-- is a setoid X equipped with a structure map α : F X → X. This is the
-- foundation for defining initial algebras and recursive data types.
module QIT.Algebra.Base {ℓCo ℓCh ℓCe} {C : Category ℓCo ℓCh ℓCe} (F : Functor C C) where


-- Define an algebra over a setoid endofunctor.
-- This is just a setoid X paired with a homomorphism:
--    α : F X → X
-- This is used for defining initial algebras.

private
  module C = Category C
  module F = Functor F

-- An F-algebra consists of a setoid carrier X and a structure map α : F X → X.
-- The structure map gives meaning to the functor's operations on the carrier.
-- For example, if F represents tree operations, α tells us how to build trees.
record Algebra : Set (ℓCo ⊔ ℓCh) where
  constructor mkAlg
  field
    -- The carrier setoid
    X : C.Obj
    -- Structure map: interprets F-structure as elements of X
    α : C [ F.ob X , X ]

-- Homomorphism between F-algebras: a homomorphism of carriers that
-- commutes with the structure maps. If f : X → Y is an algebra homomorphism,
-- then f(α(fx)) = β(F(f)(fx)) for all fx : F X.
record Hom (Xα Yβ : Algebra) : Set (ℓCo ⊔ ℓCh ⊔ ℓCe) where
  constructor mkHom
  open Algebra Xα
  open Algebra Yβ renaming (X to Y; α to β)
  field
    -- Underlying homomorphism between carriers
    hom : C [ X , Y ]
    -- Commutativity condition: the square commutes
    comm : C [ (β C.∘ F.hom hom) ≈ (hom C.∘ α) ]

-- An initial algebra has a unique homomorphism to every other algebra.
-- This property characterizes recursive data types: the initial algebra
-- gives the "freely generated" elements with no additional equations.
record IsInitial (Xα : Algebra) : Set (ℓCo ⊔ ℓCh ⊔ ℓCe) where
  constructor mkIsInitial
  open Algebra Xα
  open Hom
  field
    -- Recursor: unique map to any algebra
    rec : ∀ Yβ → Hom Xα Yβ
    -- Uniqueness: any algebra homomorphism equals the recursor
    unique : ∀ Yβ → (f : Hom Xα Yβ) → C [ f .hom ≈ rec Yβ .hom ]
