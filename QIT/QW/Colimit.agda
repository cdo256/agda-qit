open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid

-- Define colimits of diagrams indexed by preorders.
-- A colimit is the "union" of all objects in a diagram, identifying elements
-- that become equal under the diagram's morphisms. This provides the categorical
-- construction used to build quotient types from staged approximations.
module QIT.QW.Colimit {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  (ℓD ℓD' : Level)
  (P : ≈.Diagram ≤p ℓD ℓD')
  where

  private
    module ≤ = IsPreorder (≤p .proj₂)
    _≤_ : BinaryRel I ℓ≤
    _≤_ = ≤p .proj₁

  open ≈.Diagram P renaming (D-ob to P̂)

  -- Extract underlying function from diagram morphism
  Pf : ∀ {i j} (p : i ≤ j) → (⟨ P̂ i ⟩ → ⟨ P̂ j ⟩)
  Pf p = to
    where open ≈.Hom (D-hom p)

  -- Carrier of the colimit: disjoint union of all objects in the diagram.
  -- Elements are tagged by their stage index i and contain a value from P̂ i.
  Colim₀ : Set (ℓI ⊔ ℓD)
  Colim₀ = Σ[ i ∈ I ] ⟨ P̂ i ⟩

  -- Colimit equivalence relation: identifies elements across diagram morphisms.
  -- This is the minimal equivalence relation that makes diagram morphisms
  -- into equivalences in the colimit.
  data _≈ˡ_ : Colim₀ → Colim₀ → Prop (ℓ≤ ⊔ ℓI ⊔ ℓD ⊔ ℓD') where
    -- Respect equivalence within each stage
    ≈lstage : ∀ i → {x x' : ⟨ P̂ i ⟩} → P̂ i [ x ≈ x' ]
            → (i , x) ≈ˡ (i , x')
    -- Diagram morphisms become equivalences: x ≈ Pf p x
    ≈lstep  : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩) → (i , x) ≈ˡ (j , Pf p x)
    -- Equivalence relation structure
    ≈lsym   : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
    ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u

  -- Eliminator for colimit equivalence relation
  recˡ : ∀ {ℓ} (C : ∀ {s t} → s ≈ˡ t → Prop ℓ)
       → (c-stage : ∀ i {x x'} (e : P̂ i [ x ≈ x' ]) → C (≈lstage i e))
       → (c-step  : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩) → C (≈lstep p x))
       → (c-sym   : ∀ {s t} (r : s ≈ˡ t) → C r → C (≈lsym r))
       → (c-trans : ∀ {s t u} (r₁ : s ≈ˡ t) (r₂ : t ≈ˡ u) → C r₁ → C r₂ → C (≈ltrans r₁ r₂))
       → ∀ {s t} (r : s ≈ˡ t) → C r
  recˡ C c-stage c-step c-sym c-trans = go
    where
      go : ∀ {s t} (r : s ≈ˡ t) → C r
      go (≈lstage i e)    = c-stage i e
      go (≈lstep p x)     = c-step p x
      go (≈lsym r)        = c-sym r (go r)
      go (≈ltrans r₁ r₂)  = c-trans r₁ r₂ (go r₁) (go r₂)

  -- Reflexivity follows from stage reflexivity
  ≈lrefl : ∀ {t} → t ≈ˡ t
  ≈lrefl {i , x} = ≈lstage i (P̂ i .refl)
    where open ≈.Setoid

  -- Prove that ≈ˡ is an equivalence relation
  equiv : IsEquivalence _≈ˡ_
  equiv = record
    { refl  = ≈lrefl
    ; sym   = ≈lsym
    ; trans = ≈ltrans
    }
    where open ≈.Setoid

  -- The colimit setoid: disjoint union quotiented by the colimit relation
  Colim : Setoid (ℓI ⊔ ℓD) (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD')
  Colim = record
    { Carrier       = Colim₀
    ; _≈_           = _≈ˡ_
    ; isEquivalence = equiv
    }

  -- Cocones: setoids equipped with morphisms from each diagram object
  -- that commute with diagram morphisms. These are the "candidates" for
  -- being colimits - they represent ways to "collect" the diagram.
  record Cocone : Set (lsuc (ℓ≤ ⊔ ℓD' ⊔ ℓD ⊔ ℓI)) where
    field
      -- Target setoid
      Apex     : Setoid (ℓI ⊔ ℓD) (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD')
      -- Injection from each diagram object
      inj      : ∀ i → ≈.Hom (P̂ i) Apex
      -- Commutativity: injections respect diagram morphisms
      commutes : ∀ {i j} (p : i ≤ j)
               → (inj i) ≈h (inj j ≈.∘ D-hom p)

  open Cocone

  -- The canonical cocone into our colimit construction.
  -- This includes each P̂ i into the disjoint union Colim.
  LimitCocone : Cocone
  LimitCocone = record
    { Apex     = Colim
    ; inj      = λ i → record { to = λ x → i , x ; cong = ≈lstage i }
    ; commutes = λ p {x = x} → ≈lstep p x
    }

  -- Morphisms between cocones: homomorphisms of apexes that preserve injections
  record ColimMorphism (C C' : Cocone) : Set (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD') where
    field
      apexHom  : ≈.Hom (C .Apex) (C' .Apex)
      commutes : ∀ i → (apexHom ≈.∘ C .inj i) ≈h (C' .inj i)

  open ColimMorphism

  -- Universal property of colimits: there's a unique morphism to any other cocone.
  -- This characterizes the colimit as the "most efficient" way to collect the diagram.
  record isLimitingCocone (C : Cocone) : Set (lsuc ℓI ⊔ lsuc ℓ≤ ⊔ lsuc ℓD ⊔ lsuc ℓD') where
    field
      -- Mediating morphism to any cocone
      hom    : ∀ C' → ColimMorphism C C'
      -- Uniqueness of the mediating morphism
      unique : ∀ C' → (F : ColimMorphism C C')
             → F .apexHom ≈h hom C' .apexHom

  open isLimitingCocone

  open ≈.Hom

  -- Proof that our construction satisfies the universal property
  module IsLimitingCocone (C' : Cocone) where
    module C' = Cocone C'
    module ApexSetoid = ≈.Setoid C'.Apex

    private
      -- The mediating function: send (i,x) to inj_i(x) in C'
      f : ⟨ Colim ⟩ → ⟨ C'.Apex ⟩
      f (i , x) = C'.inj i .to x

    -- Prove f respects the colimit equivalence relation
    isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y) →
                   f (i , x) ApexSetoid.≈ f (j , y)
    isRespecting (≈lstage i x≈y) = C' .inj i .cong x≈y
    isRespecting (≈lstep p x)    = C'.commutes p
    isRespecting (≈lsym r)       = ApexSetoid.sym (isRespecting r)
    isRespecting (≈ltrans r s)   =
      ApexSetoid.trans (isRespecting r) (isRespecting s)

    -- The mediating morphism and proof it makes diagrams commute
    F : ColimMorphism LimitCocone C'
    F .apexHom .to  = f
    F .apexHom .cong = isRespecting
    F .commutes i {x} =
      C'.inj (LimitCocone .inj i .to x .proj₁)
        .cong (P̂ i .≈.Setoid.refl)

    -- Uniqueness: any morphism must agree with f
    unq : (G : ColimMorphism LimitCocone C') →
          ∀ x → G .apexHom .to x ApexSetoid.≈ f x
    unq G (i , x) = G .commutes i

  -- Main theorem: our construction is the colimit
  isLimitingCoconeLimitCocone : isLimitingCocone LimitCocone
  isLimitingCoconeLimitCocone = record
    { hom    = F
    ; unique = λ C' G → G .commutes _
    }
    where
    open IsLimitingCocone
