open import QIT.Prelude
open import QIT.Prop
open import QIT.Setoid
open import QIT.Container.Base
open import QIT.Functor.Base

-- Define quotient W-types: W-types equipped with a quotient relation.
-- This extends ordinary W-types with equations, allowing us to quotient
-- out unwanted distinctions. The result is the foundation for defining
-- quotient inductive types (QITs) with both constructors and equations.
module QIT.QW.W {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP)

module F = Functor F

open import QIT.Algebra.Base F

-- Underlying W-type: trees with shapes S and positions P
T : Set (ℓS ⊔ ℓP)
T = W S P

-- T forms an algebra for the container functor F.
-- The structure map is just the W-type constructor sup.
-- This makes T the initial algebra for F (before quotienting).
-- We use this algebra to define properties on T before the quotient.
T-alg : Algebra
T-alg = record
  { X = T
  ; α = sup }

module Rec (Yβ : Algebra) where
  open Algebra
  open ≈.Hom
  open Algebra Yβ renaming (X to Y; α to β)
  rec : T → Y
  rec (W.sup (s , f)) =
    β (s , λ i → rec (f i))
  -- rec-comm : (β ≈.∘ F.hom rec) ≈h (rec ≈.∘ T-α)
  -- rec-comm = Setoid.refl Y

  unique : ∀ (f : Hom T-alg Yβ) → f .Hom.hom ≈h rec
  unique f {sup (s , g)} =
    f.hom .to (W.sup (s , g))
      ≈⟨ sym f.comm ⟩
    β.to (s , λ i → f.hom .to (g i)) 
      ≈⟨ β.cong (F-Ob.mk≈ꟳ ≡.refl λ (i : P s) → unique f {g i}) ⟩
    β.to (s , λ i → rec₀ (g i)) 
      ≈⟨ refl ⟩
    rec₀ (W.sup (s , g)) ∎
    where
    open Setoid Y
    open ≈.≈syntax {S = Y}
    module f = Hom f

isInitialT : IsInitial T-alg
isInitialT = record
  { rec = λ Yβ → record
    { hom = rec Yβ
    ; comm = λ {x} → rec-comm Yβ {x} }
  ; unique = unique }
  where
  open Rec
