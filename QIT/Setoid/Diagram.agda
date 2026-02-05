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
    D-ob : ∀ (i : I) → Setoid ℓD ℓD'

    -- Morphism mapping: order relations become homomorphisms
    D-hom : ∀ {i j} → (p : i ≤ j) → Hom (D-ob i) (D-ob j)

    -- Functorial laws: preserve identity and composition
    D-id : ∀ {i : I}
         → D-hom (≤.refl) ≈h (idHom {S = D-ob i})
    D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
           → D-hom (≤.trans p q) ≈h (D-hom q ∘h D-hom p)

-- Functor composition with diagrams: F ∘ P applies functor F to diagram P.
-- If P : I → Setoid and F : Setoid → Setoid, then F ∘ P : I → Setoid.
-- This lets us transform entire diagrams by applying functors pointwise.
_∘ᴰ_ : ∀ {ℓD ℓD' ℓF ℓF'} → (F : Functor ℓD ℓD' ℓF ℓF') (P : Diagram ℓD ℓD')
    → Diagram ℓF ℓF'
_∘ᴰ_ {ℓD} {ℓD'} {ℓF} {ℓF'} F P = record
  { D-ob = D-ob
  ; D-hom = D-hom
  ; D-id = λ {i} → D-id {i}
  ; D-comp = λ {i} {j} {k} → D-comp {i} {j} {k} }
  where
  module F = Functor F
  module P = Diagram P
  open Setoid using () renaming (_≈_ to _⊢_≈_)

  -- Apply F to each object in the diagram
  D-ob : (i : I) → Setoid ℓF ℓF'
  D-ob = λ i → F.F-ob (P.D-ob i)

  -- Apply F to each morphism in the diagram
  D-hom : ∀ {i j} → ≤p .proj₁ i j
      → Hom (F.F-ob (P.D-ob i)) (F.F-ob (P.D-ob j))
  D-hom p = record
    { to = F.F-hom (P.D-hom p) .Hom.to
    ; cong = F.F-hom (P.D-hom _) .Hom.cong }

  -- F preserves identity: F(id) ≈ id
  D-id : ∀ {i} → {x : ⟨ D-ob i ⟩}
       → D-ob i ⊢ F.F-hom (P.D-hom ≤.refl) .Hom.to x ≈ x
  D-id {i} {x} = D-ob i .trans u F.F-id
    where
    open Setoid
    open Hom
    open import QIT.Relation.Binary
    u : D-ob i ⊢ (F.F-hom (P.D-hom ≤.refl) .to x)
               ≈ (F.F-hom idHom) .to x
    u = F.F-resp (P.D-hom _) idHom P.D-id

  -- F preserves composition: F(g ∘ f) ≈ F(g) ∘ F(f)
  D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
         → D-hom (≤.trans p q) ≈h (D-hom q ∘h D-hom p)
  D-comp {i} {j} {k} p q {x} =
    begin
      to (D-hom (≤.trans p q)) x
        ≈⟨ D-ob _ .refl ⟩
      to (F.F-hom (P.D-hom (≤.trans p q))) x
        ≈⟨ F.F-resp (P.D-hom _) (P.D-hom _ ∘h P.D-hom _)
                    (P.D-comp p q) ⟩
      to (F.F-hom (P.D-hom q ∘h P.D-hom p )) x
        ≈⟨ F.F-comp (P.D-hom _) (P.D-hom _) ⟩
      to (D-hom q ∘h D-hom p) x ∎
    where
    open ≈syntax {S = D-ob k}
    open Setoid
    open Hom
    open import QIT.Relation.Binary
