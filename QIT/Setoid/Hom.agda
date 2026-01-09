open import QIT.Prelude
open import QIT.Setoid.Base

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

-- Equivalence relation on homomorphisms: pointwise equivalence in codomain.
-- Two homomorphisms f, g are equivalent if f(x) ≈_T g(x) for all x.
-- This is extensional equality for functions between setoids.
_≈h_ : ∀ {ℓS ℓS' ℓT ℓT'} → {S : Setoid ℓS ℓS'} {T : Setoid ℓT ℓT'}
     → (f g : Hom S T) → Prop (ℓS ⊔ ℓT')
_≈h_ {T = T} f g = ∀ {x} → f.to x T.≈ g.to x
  where
  module T = Setoid T
  module f = Hom f
  module g = Hom g

-- Composition of setoid homomorphisms: (f ∘ g)(x) = f(g(x)).
-- Congruence follows from both f and g preserving equivalence.
-- Makes setoids form a category with idHom as identity.
infixr 1 _∘_
_∘_ : ∀ {ℓA ℓA' ℓB ℓB' ℓC ℓC' }
    → {A : Setoid ℓA ℓA'} {B : Setoid ℓB ℓB'} {C : Setoid ℓC ℓC'}
    → Hom B C → Hom A B → Hom A C
f ∘ g = record
  { to  = λ x → f.to (g.to x)
  ; cong = λ x≈y → f.cong (g.cong x≈y)
  }
  where
  module f = Hom f
  module g = Hom g
