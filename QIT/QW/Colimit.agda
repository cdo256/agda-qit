open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Set.Base
open import QIT.Functor.Base
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set

-- Define colimits of diagrams indexed by preorders.
-- A colimit is the "union" of all objects in a diagram, identifying elements
-- that become equal under the diagram's morphisms. This provides the categorical
-- construction used to build quotient types from staged approximations.
module QIT.QW.Colimit {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  (ℓD ℓD' : Level)
  (P : Functor (PreorderCat I ≤p) (SetCat (ℓD ⊔ ℓD')))
  where

  private
    module ≤ = IsPreorder (≤p .proj₂)
    _≤_ : BinaryRel I ℓ≤
    _≤_ = ≤p .proj₁

  open Functor P using () renaming (ob to P̂)
  module P = Functor P

  -- Extract underlying function from diagram morphism
  Pf : ∀ {i j} (p : i ≤ j) → (P̂ i → P̂ j)
  Pf p = P.hom (box p)

  -- Carrier of the colimit: disjoint union of all objects in the diagram.
  -- Elements are tagged by their stage index i and contain a value from P̂ i.
  Colim₀ : Set (ℓI ⊔ ℓD ⊔ ℓD')
  Colim₀ = Σ[ i ∈ I ] P̂ i

  -- Colimit equivalence relation: identifies elements across diagram morphisms.
  -- This is the minimal equivalence relation that makes diagram morphisms
  -- into equivalences in the colimit.
  data _≈ˡ_ : Colim₀ → Colim₀ → Prop (ℓ≤ ⊔ ℓI ⊔ ℓD ⊔ ℓD') where
    -- Respect equivalence within each stage
    ≈lstage : ∀ i → {x x' : P̂ i} → x ≡ x'
            → (i , x) ≈ˡ (i , x')
    -- Diagram morphisms become equivalences: x ≈ Pf p x
    ≈lstep  : ∀ {i j} (p : i ≤ j) (x : P̂ i) → (i , x) ≈ˡ (j , Pf p x)
    -- Equivalence relation structure
    ≈lsym   : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
    ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u

  -- Eliminator for colimit equivalence relation
  recˡ : ∀ {ℓ} (C : ∀ {s t} → s ≈ˡ t → Prop ℓ)
       → (c-stage : ∀ i {x x'} (e : x ≡ x') → C (≈lstage i e))
       → (c-step  : ∀ {i j} (p : i ≤ j) (x : P̂ i) → C (≈lstep p x))
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
  ≈lrefl {i , x} = ≈lstage i ≡.refl
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
  Colim : Setoid (ℓI ⊔ ℓD ⊔ ℓD') (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD')
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
      Apex     : Set (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD')
      -- Injection from each diagram object
      inj      : ∀ i → P̂ i → Apex
      -- Commutativity: injections respect diagram morphisms
      commutes : ∀ {i j} (p : i ≤ j)
               → inj i ≡ (inj j ∘ P.hom (box p))

  open Cocone
  open SetoidQuotient Colim

  -- The canonical cocone into our colimit construction.
  -- This includes each P̂ i into the disjoint union Colim.
  LimitCocone : Cocone
  LimitCocone = record
    { Apex     = Colim /≈
    ; inj      = λ i x → [ i , x ]  
    ; commutes = λ p → ≡.funExt λ x → ≈[ ≈lstep p x ]
    }

  -- Morphisms between cocones: homomorphisms of apexes that preserve injections
  record ColimMorphism (C C' : Cocone) : Set (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD') where
    field
      apexHom  : (C .Apex) → (C' .Apex)
      commutes : ∀ i → (apexHom ∘ C .inj i) ≡ (C' .inj i)

  open ColimMorphism

  -- Universal property of colimits: there's a unique morphism to any other cocone.
  -- This characterizes the colimit as the "most efficient" way to collect the diagram.
  record isLimitingCocone (C : Cocone) : Set (lsuc ℓI ⊔ lsuc ℓ≤ ⊔ lsuc ℓD ⊔ lsuc ℓD') where
    field
      -- Mediating morphism to any cocone
      hom    : ∀ C' → ColimMorphism C C'
      -- Uniqueness of the mediating morphism
      unique : ∀ C' → (F : ColimMorphism C C')
             → ∀ x̃ → F .apexHom x̃ ≡ hom C' .apexHom x̃

  open isLimitingCocone

  open ≈.Hom

  -- Proof that our construction satisfies the universal property
  module IsLimitingCocone (C' : Cocone) where
    module C' = Cocone C'

    -- The mediating function: send (i,x) to inj_i(x) in C'
    f₀ : Colim₀ → C'.Apex
    f₀ (i , x) = C'.inj i x

    -- Prove f respects the colimit equivalence relation
    isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y) →
                   f₀ (i , x) ≡ f₀ (j , y)
    isRespecting (≈lstage i x≈y) = ≡.cong (C'.inj i) x≈y
    isRespecting {i} {j} {x} {y} (≈lstep p x)    = q
      where
      q : C'.inj i x ≡ C'.inj j y
      q = ≡.funExt⁻ (C'.commutes p) x
    isRespecting (≈lsym r)       = ≡.sym (isRespecting r)
    isRespecting (≈ltrans r s)   =
      ≡.trans (isRespecting r) (isRespecting s)

    f : Colim /≈ → C'.Apex
    f = quot-rec f₀ isRespecting

    -- The mediating morphism and proof it makes diagrams commute
    F : ColimMorphism LimitCocone C'
    F .apexHom  = f
    F .commutes i = ≡.refl

    -- Uniqueness: any morphism must agree with f
    unq : (G : ColimMorphism LimitCocone C') →
          ∀ x̃ → G .apexHom x̃ ≡ f x̃
    unq G = quot-elimp (λ x̃ → G .apexHom x̃ ≡ f x̃) λ (i , x) → q i x
      where
      q : ∀ i x → G .apexHom [ i , x ] ≡ C'.inj i x
      q i = ≡.funExt⁻ (G .commutes i)

  -- Main theorem: our construction is the colimit
  isLimitingCoconeLimitCocone : isLimitingCocone LimitCocone
  isLimitingCoconeLimitCocone = record
    { hom    = F
    ; unique = unq
    }
    where
    open IsLimitingCocone
