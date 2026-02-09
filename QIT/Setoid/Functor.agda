open import QIT.Prelude
open import QIT.Setoid.Base
open import QIT.Setoid.Hom

-- Define functors between setoid categories. A functor F : C → D
-- maps objects to objects and morphisms to morphisms while preserving
-- identity and composition. Here we focus on endofunctors in the
-- category of setoids.
module QIT.Setoid.Functor where

-- An endofunctor in the category of setoids maps setoids to setoids
-- and homomorphisms to homomorphisms, preserving categorical structure.
-- This is used to define algebraic signatures and their interpretations.
-- Note ℓd and ℓd' are the domain levels while ℓc and ℓc' are the setoid
-- levels for the codomain.
record Functor ℓd ℓd' ℓc ℓc' : Set (lsuc ℓd ⊔ lsuc ℓd' ⊔ lsuc ℓc ⊔ lsuc ℓc') where
  private
    D = Setoid ℓd ℓd'
  field
    -- Object mapping: sends setoids to setoids
    ob : ∀ (S : D) → Setoid ℓc ℓc'

    -- Morphism mapping: sends homomorphisms to homomorphisms
    hom : ∀ {S T : D} → Hom S T → Hom (ob S) (ob T)

    -- Preserves identity: F(id) ≈ id
    id : ∀ {S : D} → hom idHom ≈h idHom {S = ob S}

    -- Preserves composition: F(g ∘ f) ≈ F(g) ∘ F(f)
    comp : ∀ {S T U : D} → (f : Hom S T) → (g : Hom T U)
           → hom (g ∘ f) ≈h (hom g ∘ hom f)

    -- Respects homomorphism equivalence: if f ≈ g then F(f) ≈ F(g)
    resp : ∀ {S T} (f g : Hom S T) → f ≈h g → hom f ≈h hom g
