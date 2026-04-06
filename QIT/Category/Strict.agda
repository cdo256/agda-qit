module QIT.Category.Strict where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation
open import QIT.Relation.Binary
open import QIT.Category.Base using (Category)
open import QIT.Setoid.Base hiding (_[_≈_])

-- Adapted from 'Agda Categories', changed to make BinaryRel Prop-valued, removed hom-setoid.
record StrictCategory (o ℓ : Level) : Set (lsuc (o ⊔ ℓ)) where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    -- We add a symmetric proof of associativity so that the opposite category of the
    -- opposite category is definitionally equal to the original category. See how
    -- `op` is implemented.
    sym-assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f
    -- We add a proof of "neutral" identity proof, in order to ensure the opposite of
    -- constant functor is definitionally equal to itself.
    identity² : ∀ {A} → id ∘ id {A} ≡ id {A}

  ∃!hom : ∀ {ℓP A B} → (P : A ⇒ B → Prop ℓP) → Set (ℓ ⊔ ℓP)
  ∃!hom {A = A} {B} = ∃! ((A ⇒ B) /≡)

  -- When a category is quantified, it is convenient to refer to the levels from a module,
  -- so we do not have to explicitly quantify over a category when universe levels do not
  -- play a big part in a proof (which is the case probably all the time).
  o-level : Level
  o-level = o

  ℓ-level : Level
  ℓ-level = ℓ


module StrictNotation {o ℓ : Level} where
  -- Convenience functions for working over multiple categories at once:
  -- C [ x , y ] (for x y objects of C) - Hom_C(x , y)
  -- C [ f ∘ g ] (for f g composable arrows of C) - composition in C
  infix 10  _[_,_] _[_∘_]

  _[_,_] : (C : StrictCategory o ℓ) → (X : StrictCategory.Obj C) → (Y : StrictCategory.Obj C) → Set ℓ
  _[_,_] = StrictCategory._⇒_

  _[_∘_] : (C : StrictCategory o ℓ) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
  _[_∘_] = StrictCategory._∘_

  _op : (C : StrictCategory o ℓ) → StrictCategory o ℓ
  C op = record
    { Obj = Obj
    ; _⇒_ = λ A B → B ⇒ A
    ; id = id
    ; _∘_ = λ g f → f ∘ g
    ; assoc = sym-assoc
    ; sym-assoc = assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; identity² = identity²
    }
    where open StrictCategory C

StrictCategory→Category : ∀ {ℓCo ℓCh} → StrictCategory ℓCo ℓCh → Category ℓCo ℓCh ℓCh
StrictCategory→Category C = record
  { Obj = Obj
  ; _⇒_ = _⇒_
  ; _≈_ = _≡_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = λ {A} → identityˡ
  ; equiv = isEquiv-≡ _
  ; ∘-resp-≈ = ≡.cong₂ _∘_
  }
  where open StrictCategory C
