open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid.Base
open import QIT.Setoid.Hom renaming (_∘_ to _∘h_)
open import QIT.Setoid.Functor

-- Define diagrams indexed by preordered sets and their functor composition.
-- A diagram is a functor from a preorder category to setoids, used to set up
-- colimit constructions. This provides the categorical framework for building
-- quotient types as colimits of staged approximations.
module QIT.Setoid.Diagram {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  where

private
  module ≤ = IsPreorder (≤p .proj₂)
  _≤_ : BinaryRel I ℓ≤
  _≤_ = ≤p .proj₁

-- A diagram over preorder I: assigns setoids to objects and homomorphisms to morphisms.
-- This is a covariant functor from the preorder category I to the category of setoids.
-- Diagrams are used to organize families of setoids with transition maps.
record Diagram ℓD ℓD' : Set (ℓ≤ ⊔ ℓI ⊔ lsuc ℓD ⊔ lsuc ℓD') where
  field
    -- Object mapping: each index gets a setoid
    ob : ∀ (i : I) → Setoid ℓD ℓD'

    -- Morphism mapping: order relations become homomorphisms
    hom : ∀ {i j} → (p : i ≤ j) → Hom (ob i) (ob j)

    -- Functorial laws: preserve identity and composition
    id : ∀ {i : I}
         → hom (≤.refl) ≈h (idHom {S = ob i})
    comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
           → hom (≤.trans p q) ≈h (hom q ∘h hom p)

-- Functor composition with diagrams: F ∘ P applies functor F to diagram P.
-- If P : I → Setoid and F : Setoid → Setoid, then F ∘ P : I → Setoid.
-- This lets us transform entire diagrams by applying functors pointwise.
_∘ᴰ_ : ∀ {ℓD ℓD' ℓF ℓF'} → (F : Functor ℓD ℓD' ℓF ℓF') (P : Diagram ℓD ℓD')
    → Diagram ℓF ℓF'
_∘ᴰ_ {ℓD} {ℓD'} {ℓF} {ℓF'} F P = record
  { ob = ob
  ; hom = hom
  ; id = λ {i} → id {i}
  ; comp = λ {i} {j} {k} → comp {i} {j} {k} }
  where
  module F = Functor F
  module P = Diagram P
  open Setoid using () renaming (_≈_ to _⊢_≈_)

  -- Apply F to each object in the diagram
  ob : (i : I) → Setoid ℓF ℓF'
  ob = λ i → F.F-ob (P.ob i)

  -- Apply F to each morphism in the diagram
  hom : ∀ {i j} → ≤p .proj₁ i j
      → Hom (F.F-ob (P.ob i)) (F.F-ob (P.ob j))
  hom p = record
    { to = F.F-hom (P.hom p) .Hom.to
    ; cong = F.F-hom (P.hom _) .Hom.cong }

  -- F preserves identity: F(id) ≈ id
  id : ∀ {i} → {x : ⟨ ob i ⟩}
       → ob i ⊢ F.F-hom (P.hom ≤.refl) .Hom.to x ≈ x
  id {i} {x} = ob i .trans u F.F-id
    where
    open Setoid
    open Hom
    open import QIT.Relation.Binary
    u : ob i ⊢ (F.F-hom (P.hom ≤.refl) .to x)
               ≈ (F.F-hom idHom) .to x
    u = F.F-resp (P.hom _) idHom P.id

  -- F preserves composition: F(g ∘ f) ≈ F(g) ∘ F(f)
  comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
         → hom (≤.trans p q) ≈h (hom q ∘h hom p)
  comp {i} {j} {k} p q {x} =
    begin
      to (hom (≤.trans p q)) x
        ≈⟨ ob _ .refl ⟩
      to (F.F-hom (P.hom (≤.trans p q))) x
        ≈⟨ F.F-resp (P.hom _) (P.hom _ ∘h P.hom _)
                    (P.comp p q) ⟩
      to (F.F-hom (P.hom q ∘h P.hom p )) x
        ≈⟨ F.F-comp (P.hom _) (P.hom _) ⟩
      to (hom q ∘h hom p) x ∎
    where
    open ≈syntax {S = ob k}
    open Setoid
    open Hom
    open import QIT.Relation.Binary
