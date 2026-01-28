open import QIT.Prelude

-- Module for creating adapter algebras that work with Container functors at higher universe levels
-- while keeping the same underlying carrier type. This allows reusing algebras defined at lower
-- levels in contexts requiring higher levels, avoiding --type-in-type.
--
-- The key insight: instead of lifting the carrier, we create an adapter that translates
-- between the low-level and high-level functor representations while preserving semantics.
module QIT.Setoid.Algebra.Lift
  {ℓS ℓP : Level} (S : Set ℓS) (P : S → Set ℓP)
  (ℓV : Level)  -- The additional level we need to accommodate
  where

open import QIT.Setoid as ≈
open import QIT.Container.Base

-- Import Container functors at both level configurations
import QIT.Container.Functor S P (ℓS ⊔ ℓP) (ℓS ⊔ ℓP) as FSmall
import QIT.Container.Functor S P (ℓS ⊔ ℓP ⊔ ℓV) (ℓS ⊔ ℓP ⊔ ℓV) as FBig

-- Type aliases for the algebra types
AlgSmall = ≈.Algebra FSmall.F
AlgBig = ≈.Algebra FBig.F

-- Create an adapter algebra that works with the higher-level functor
-- but delegates operations to the original algebra at lower levels
adaptAlgebra : AlgSmall → AlgBig
adaptAlgebra smallAlg = record { X = X-big ; α = α-big }
  where
    open ≈.Algebra smallAlg renaming (X to X-small; α to α-small)

    -- The big setoid uses lifted carrier but provides transparent access
    X-big : Setoid (ℓS ⊔ ℓP ⊔ ℓV) (ℓS ⊔ ℓP ⊔ ℓV)
    X-big = record
      { Carrier = Lift ℓV ⟨ X-small ⟩  -- Lifted carrier
      ; _≈_ = λ x y → LiftP ℓV (X-small [ lower x ≈ lower y ])  -- Lift the equality relation
      ; isEquivalence = record
        { refl = liftp (≈.Setoid.refl X-small)
        ; sym = λ (liftp p) → liftp (≈.Setoid.sym X-small p)
        ; trans = λ (liftp p) (liftp q) → liftp (≈.Setoid.trans X-small p q)
        }
      }

    -- Helper to lower LiftP
    lowerP : ∀ {ℓ a} {A : Prop a} → LiftP ℓ A → A
    lowerP (liftp x) = x

    -- The structure map: convert big functor input to small functor input,
    -- apply the small algebra, then lift the result
    op-big : ⟨ FBig.F-ob X-big ⟩ → ⟨ X-big ⟩
    op-big (s , k) = lift (≈.Hom.to α-small (s , λ p → lower (k p)))

    -- Congruence: if big inputs are equal, then outputs are equal
    cong-big : {x y : ⟨ FBig.F-ob X-big ⟩} →
               FBig.F-ob X-big [ x ≈ y ] →
               X-big [ op-big x ≈ op-big y ]
    cong-big {s , k} {s' , k'} (FBig.F-Ob.mk≈ꟳ eqS eqK) =
      liftp (≈.Hom.cong α-small (FSmall.F-Ob.mk≈ꟳ eqS (λ p → lowerP (eqK p))))

    -- The big structure map
    α-big : ≈.Hom (FBig.F-ob X-big) X-big
    α-big = record
      { to = op-big
      ; cong = cong-big
      }

-- Export the main function with a cleaner name
liftAlgebra = adaptAlgebra
