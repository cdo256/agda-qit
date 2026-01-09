open import QIT.Prelude
open import QIT.Setoid
open import QIT.Container.Base
open import QIT.QW.Signature

-- Define quotient W-types: W-types equipped with a quotient relation.
-- This extends ordinary W-types with equations, allowing us to quotient
-- out unwanted distinctions. The result is the foundation for defining
-- quotient inductive types (QITs) with both constructors and equations.
module QIT.QW.W {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where

open Sig sig
open import QIT.Container.Functor S P (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)

-- Underlying W-type: trees with shapes S and positions P
T : Set (ℓS ⊔ ℓP)
T = W S P

-- View T as a setoid with propositional equality (without a quotient)
T̃ : Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)
T̃ = ≡setoid T

-- T forms an algebra for the container functor F.
-- The structure map is just the W-type constructor sup.
-- This makes T the initial algebra for F (before quotienting).
-- We use this algebra to define properties on T before the quotient.
T-alg : ≈.Algebra F
T-alg = record
  { X = T̃
  ; α = record
    { to = sup
    ; cong = α-cong } }
  where
  open F-Ob T̃

  -- Congruence: sup respects equivalence in the functor interpretation
  α-cong : ∀ {sf} {tg} → sf ≈ꟳ tg → sup sf ≡p sup tg
  α-cong {s , f} {s , g} (mk≈ꟳ ≡.refl snd≈) = q (funExtp snd≈)
    where
    q : f ≡p g → sup (s , f) ≡p sup (s , g)
    q ∣ ≡.refl ∣ = ∣ ≡.refl ∣
