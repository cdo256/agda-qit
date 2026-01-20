open import QIT.Prelude
open import QIT.Setoid
open import QIT.Container.Base

-- Define quotient W-types: W-types equipped with a quotient relation.
-- This extends ordinary W-types with equations, allowing us to quotient
-- out unwanted distinctions. The result is the foundation for defining
-- quotient inductive types (QITs) with both constructors and equations.
module QIT.QW.W {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓA ℓA' : Level) where

open import QIT.Container.Functor S P (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)

-- Underlying W-type: trees with shapes S and positions P
T : Set (ℓS ⊔ ℓP)
T = W S P

-- View T as a setoid with propositional equality (without a quotient)
T̃ : Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)
T̃ = T /≡

module _ where
  -- Congruence: sup respects equivalence in the functor interpretation
  α-cong : ∀ {sf} {tg} → F-ob T̃ [ sf ≈ tg ] → sup sf ≡p sup tg
  α-cong {s , f} {s , g} (F-Ob.mk≈ꟳ ≡.refl snd≈) = q (funExtp snd≈)
    where
    open F-Ob T̃
    q : f ≡p g → sup (s , f) ≡p sup (s , g)
    q ∣ ≡.refl ∣ = ∣ ≡.refl ∣
  T-α : ≈.Hom (F-ob T̃) T̃
  T-α = record
    { to = sup
    ; cong = α-cong }

-- T forms an algebra for the container functor F.
-- The structure map is just the W-type constructor sup.
-- This makes T the initial algebra for F (before quotienting).
-- We use this algebra to define properties on T before the quotient.
T-alg : ≈.Algebra F
T-alg = record
  { X = T̃
  ; α = T-α }

module Rec (Yβ : ≈.Algebra F) where
  open ≈.Algebra hiding (sup)
  open ≈.Hom
  open ≈.Algebra Yβ renaming (X to Y; α to β; sup to β₀)
  rec₀ : ⟨ T̃ ⟩ → ⟨ Y ⟩
  rec₀ (W.sup (s , f)) =
    β₀ (s , λ i → rec₀ (f i)) 
  rec-cong : ∀ {x y} → T̃ [ x ≈ y ] → Y [ rec₀ x ≈ rec₀ y ]
  rec-cong reflp = ≡→≈ Y ≡.refl
  rec : ≈.Hom T̃ Y
  rec = record { to = rec₀ ; cong = rec-cong }
  rec-comm : (β ≈.∘ F-mor rec) ≈h (rec ≈.∘ T-α)
  rec-comm = Setoid.refl Y

  open ≈.Alg.Hom
  unique : ∀ (f : ≈.Alg.Hom F T-alg Yβ) → f .hom ≈h rec
  unique f {sup (s , g)} =
    f.hom .to (W.sup (s , g))
      ≈⟨ sym f.comm ⟩
    β₀ (s , λ i → f.hom .to (g i)) 
      ≈⟨ β.cong (F-Ob.mk≈ꟳ ≡.refl λ i → unique f {g i}) ⟩
    β₀ (s , λ i → rec₀ (g i)) 
      ≈⟨ refl ⟩
    rec₀ (W.sup (s , g)) ∎
    where
    open Setoid Y
    open ≈.≈syntax {S = Y}
    module f = ≈.Alg.Hom f
    module β = ≈.Hom β

isInitialT : ≈.Alg.IsInitial F T-alg
isInitialT = record
  { rec = λ Yβ → record { hom = rec Yβ ; comm = λ {x} → rec-comm Yβ {x} }
  ; unique = unique }
  where
  open Rec
