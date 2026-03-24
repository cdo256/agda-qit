module QIT.Category.SetoidEnriched where

open import QIT.Prelude
open import QIT.Category.Base
open import QIT.Relation
open import QIT.Setoid

-- Setoid enriched category
record Category≈ (o ℓ eo eℓ : Level)
  : Set (lsuc (o ⊔ ℓ ⊔ eo ⊔ eℓ)) where
  eta-equality
  infix  4 _≈⃗_ _≈⁰_ _⇒_
  infixr 9 _∘_

  field
    -- Objects + object equality (a setoid)
    Obj  : Set o
    _≈⁰_ : BinaryRel Obj eo

    -- Morphisms + morphism equality (a setoid, per hom)
    _⇒_  : Obj → Obj → Set ℓ
    _≈⃗_ : ∀ {A B} → BinaryRel (A ⇒ B) eℓ

    -- Identities + composition
    id   : ∀ {A} → (A ⇒ A)
    _∘_  : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  -- Equivalence structure on ≈⁰ and ≈⃗
  field
    equiv⁰ : Binary.IsEquivalence _≈⁰_
    equiv⃗ : ∀ {A B} → Binary.IsEquivalence (_≈⃗_ {A} {B})

  module Equiv⁰ = Binary.IsEquivalence equiv⁰
  open Equiv⁰ renaming (refl to refl⁰; sym to sym⁰; trans to trans⁰)

  module Equiv⃗ {A B : Obj} = Binary.IsEquivalence (equiv⃗ {A} {B})
  open Equiv⃗ renaming (refl to refl⃗; sym to sym⃗; trans to trans⃗)

  -- Transport/reindexing of morphisms along object equalities
  field
    subst⁰ : ∀ {A B C D} → A ≈⁰ B → C ≈⁰ D → (A ⇒ C) → (B ⇒ D)

    -- subst respects morphism equality
    subst-resp-≈⃗ :
      ∀ {A B C D} (p : A ≈⁰ B) (q : C ≈⁰ D) {f g : A ⇒ C} →
      f ≈⃗ g → subst⁰ p q f ≈⃗ subst⁰ p q g

    -- functoriality/coherence of subst
    subst-refl :
      ∀ {A C} {f : A ⇒ C} →
      subst⁰ (refl⁰ {A}) (refl⁰ {C}) f ≈⃗ f

    subst-trans :
      ∀ {A B C D E F}
        (p₁ : A ≈⁰ B) (p₂ : B ≈⁰ C)
        (q₁ : D ≈⁰ E) (q₂ : E ≈⁰ F)
        (f  : A ⇒ D) →
      subst⁰ p₂ q₂ (subst⁰ p₁ q₁ f)
        ≈⃗ subst⁰ (trans⁰ p₁ p₂) (trans⁰ q₁ q₂) f

  -- Category laws (up to ≈⃗)
  field
    assoc :
      ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
      (h ∘ g) ∘ f ≈⃗ h ∘ (g ∘ f)

    sym-assoc :
      ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
      h ∘ (g ∘ f) ≈⃗ (h ∘ g) ∘ f

    identityˡ :
      ∀ {A B} {f : A ⇒ B} → id ∘ f ≈⃗ f

    identityʳ :
      ∀ {A B} {f : A ⇒ B} → f ∘ id ≈⃗ f

    identity² :
      ∀ {A} → id ∘ id {A} ≈⃗ id {A}

    ∘-resp-≈ :
      ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} →
      f ≈⃗ h → g ≈⃗ i → f ∘ g ≈⃗ h ∘ i

  -- Compatibility of subst with id and composition
  field
    subst-id⁰ :
      ∀ {A B} (p : A ≈⁰ B) →
      subst⁰ p p (id {A}) ≈⃗ id {B}

    subst-∘ :
      ∀ {A A' B B' C C'}
        (pA : A ≈⁰ A') (pB : B ≈⁰ B') (pC : C ≈⁰ C')
        (g  : B ⇒ C) (f : A ⇒ B) →
      subst⁰ pA pC (g ∘ f)
        ≈⃗ (subst⁰ pB pC g) ∘ (subst⁰ pA pB f)

  ∘-resp-≈ˡ :
    ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} →
    f ≈⃗ h → f ∘ g ≈⃗ h ∘ g
  ∘-resp-≈ˡ pf = ∘-resp-≈ pf refl⃗

  ∘-resp-≈ʳ :
    ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} →
    f ≈⃗ h → g ∘ f ≈⃗ g ∘ h
  ∘-resp-≈ʳ pf = ∘-resp-≈ refl⃗ pf

  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈⃗_
    ; isEquivalence = equiv⃗
    }

  -- When a category is quantified, it is convenient to refer to the levels from a module,
  -- so we do not have to explicitly quantify over a category when universe levels do not
  -- play a big part in a proof (which is the case probably all the time).
  o-level : Level
  o-level = o

  ℓ-level : Level
  ℓ-level = ℓ

  eo-level : Level
  eo-level = eo

  eℓ-level : Level
  eℓ-level = eℓ

Category≈→Category : ∀ {o ℓ eo eℓ} → Category≈ o ℓ eo eℓ → Category o ℓ eℓ
Category≈→Category C = record
  { Obj = Obj
  ; _⇒_ = _⇒_
  ; _≈_ = _≈⃗_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = equiv⃗
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where open Category≈ C

-- A functor between setoid-enriched categories (objects + homs are setoids,
-- with explicit transport on homs), preserving everything up to ≈⃗.
record Functor≈
  {o₁ ℓ₁ eo₁ eℓ₁ o₂ ℓ₂ eo₂ eℓ₂ : Level}
  (C : Category≈ o₁ ℓ₁ eo₁ eℓ₁)
  (D : Category≈ o₂ ℓ₂ eo₂ eℓ₂)
  : Set (lsuc (o₁ ⊔ ℓ₁ ⊔ eo₁ ⊔ eℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ eo₂ ⊔ eℓ₂)) where
  eta-equality

  private
    module C = Category≈ C
    module D = Category≈ D

  field
    -- Object and morphism maps
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → (A C.⇒ B) → (F₀ A D.⇒ F₀ B)

    -- Respect the setoid equalities
    F₀-resp-≈⁰ :
      ∀ {A B} → A C.≈⁰ B → F₀ A D.≈⁰ F₀ B

    F₁-resp-≈⃗ :
      ∀ {A B} {f g : A C.⇒ B} →
      f C.≈⃗ g → F₁ f D.≈⃗ F₁ g

    -- Preserve identities and composition up to ≈⃗
    F-id :
      ∀ {A} → F₁ (C.id {A}) D.≈⃗ D.id {F₀ A}

    F-∘ :
      ∀ {A B C'} (g : B C.⇒ C') (f : A C.⇒ B) →
      F₁ (g C.∘ f) D.≈⃗ (F₁ g) D.∘ (F₁ f)

    -- Compatibility with transport (reindexing along ≈⁰)
    --
    -- Given p : A ≈⁰ B and q : C ≈⁰ D, you can transport a morphism
    -- f : A ⇒ C to subst⁰ p q f : B ⇒ D in C.
    -- Functoriality should commute with this transport, up to ≈⃗ in D.
    F-subst⁰ :
      ∀ {A B C' D'} (p : A C.≈⁰ B) (q : C' C.≈⁰ D') (f : A C.⇒ C') →
      F₁ (C.subst⁰ p q f)
        D.≈⃗
      D.subst⁰ (F₀-resp-≈⁰ p) (F₀-resp-≈⁰ q) (F₁ f)
