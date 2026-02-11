open import QIT.Prelude
open import QIT.Prop
open import QIT.Setoid.Base
open import QIT.Relation.Binary using (IsEquivalence)

-- Define homomorphisms (structure-preserving maps) between setoids.
-- A setoid homomorphism f : S → T is a function that respects equivalence:
-- if x ≈_S y, then f(x) ≈_T f(y). This ensures the function is well-defined
-- on equivalence classes.
module QIT.Setoid.Hom where

-- A homomorphism consists of an underlying function and a proof that it
-- preserves the equivalence relation (congruence condition).
record Hom {ℓS ℓS' ℓT ℓT'}
       (S : Setoid ℓS ℓS') (T : Setoid ℓT ℓT') : Set (ℓS ⊔ ℓS' ⊔ ℓT ⊔ ℓT')
       where
  module S = Setoid S
  module T = Setoid T
  field
    -- The underlying function between carrier sets
    to : S.Carrier → T.Carrier

    -- Congruence: the function preserves equivalence relations
    cong : ∀ {x y} → x S.≈ y → to x T.≈ to y

-- The identity homomorphism maps each element to itself.
-- Provides the identity morphism for the setoid category.
idHom : ∀ {ℓ ℓ'} → {S : Setoid ℓ ℓ'} → Hom S S
idHom {S = S} = record
  { to = λ x → x
  ; cong = λ p → p }

≡Hom : ∀ {ℓX ℓY ℓY'} {X : Set ℓX} {Y : Setoid ℓY ℓY'} (f : X → ⟨ Y ⟩)
     → Hom (X /≡) Y
≡Hom {Y = Y} f = record
  { to = f
  ; cong = λ p → ≡p→≈ Y (congp f p) }

-- Equivalence relation on homomorphisms: pointwise equivalence in codomain.
-- Two homomorphisms f, g are equivalent if f(x) ≈_T g(x) for all x.
-- This is extensional equality for functions between setoids.
module _ {ℓS ℓS' ℓT ℓT'} {S : Setoid ℓS ℓS'} {T : Setoid ℓT ℓT'} where
  private
    module T = Setoid T

  _≈h_ : (f g : Hom S T) → Prop (ℓS ⊔ ℓT')
  _≈h_ f g = ∀ {x} → f.to x T.≈ g.to x
    where
    module f = Hom f
    module g = Hom g

  ≈h-refl : {f : Hom S T} → f ≈h f
  ≈h-refl = T.refl

  ≈h-sym : {f g : Hom S T} → f ≈h g → g ≈h f
  ≈h-sym p = T.sym p

  ≈h-trans : {f g h : Hom S T} → f ≈h g → g ≈h h → f ≈h h
  ≈h-trans p q = T.trans p q

  -- IsEquivalence instance for homomorphism equivalence
  ≈h-isEquivalence : IsEquivalence _≈h_
  ≈h-isEquivalence = record
    { refl = λ {f} → ≈h-refl {f = f}
    ; sym = λ {f g} → ≈h-sym {f = f} {g = g}
    ; trans = λ {f g h} → ≈h-trans {f = f} {g = g} {h = h}
    }

HomSetoid : ∀ {ℓS ℓS' ℓT ℓT'} (S : Setoid ℓS ℓS') (T : Setoid ℓT ℓT') → Setoid (ℓS ⊔ ℓS' ⊔ ℓT ⊔ ℓT') (ℓS ⊔ ℓT')
HomSetoid S T = record
  { Carrier = Hom S T
  ; _≈_ = _≈h_
  ; isEquivalence = ≈h-isEquivalence }

-- Composition of setoid homomorphisms: (f ∘ g)(x) = f(g(x)).
-- Congruence follows from both f and g preserving equivalence.
-- Makes setoids form a category with idHom as identity.
infixr 1 _∘_
_∘_ : ∀ {ℓA ℓA' ℓB ℓB' ℓC ℓC' }
    → {A : Setoid ℓA ℓA'} {B : Setoid ℓB ℓB'} {C : Setoid ℓC ℓC'}
    → Hom B C → Hom A B → Hom A C
g ∘ f = record
  { to  = λ x → g.to (f.to x)
  ; cong = λ x≈y → g.cong (f.cong x≈y)
  }
  where
  module f = Hom f
  module g = Hom g

∘-assoc : ∀ {ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD'}
        → {A : Setoid ℓA ℓA'} {B : Setoid ℓB ℓB'} {C : Setoid ℓC ℓC'} {D : Setoid ℓD ℓD'}
        → (h : Hom C D) → (g : Hom B C) → (f : Hom A B)
        → (h ∘ (g ∘ f)) ≈h ((h ∘ g) ∘ f)
∘-assoc {D = D} h g f {x} = refl
  where
  open Setoid D

∘-resp-≈ : ∀ {ℓA ℓA' ℓB ℓB' ℓC ℓC'}
         → {A : Setoid ℓA ℓA'} {B : Setoid ℓB ℓB'} {C : Setoid ℓC ℓC'}
         → {g₁ g₂ : Hom B C} → {f₁ f₂ : Hom A B}
         → (g₁≈g₂ : g₁ ≈h g₂) (f₁≈f₂ : f₁ ≈h f₂)
         → (g₁ ∘ f₁) ≈h (g₂ ∘ f₂)
∘-resp-≈ {C = C} {g₁ = g₁} g₁≈g₂ f₁≈f₂ =
  C.trans (g₁.cong f₁≈f₂) g₁≈g₂
  where
  module C = Setoid C
  module g₁ = Hom g₁

