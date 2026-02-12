module QIT.Category.Base where

open import QIT.Prelude
open import QIT.Relation
open import QIT.Setoid.Base hiding (_[_≈_])

-- Taken from 'Agda Categories', changed to make BinaryRel Prop-valued.
record Category (o ℓ e : Level) : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  eta-equality
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ
    _≈_ : ∀ {A B} → BinaryRel (A ⇒ B) e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    -- We add a symmetric proof of associativity so that the opposite category of the
    -- opposite category is definitionally equal to the original category. See how
    -- `op` is implemented.
    sym-assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    -- We add a proof of "neutral" identity proof, in order to ensure the opposite of
    -- constant functor is definitionally equal to itself.
    identity² : ∀ {A} → id ∘ id {A} ≈ id {A}
    equiv     : ∀ {A B} → Binary.IsEquivalence (_≈_ {A} {B})
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  module Equiv {A B : Obj} = Binary.IsEquivalence (equiv {A} {B})

  open Equiv

  ∘-resp-≈ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → f ∘ g ≈ h ∘ g
  ∘-resp-≈ˡ pf = ∘-resp-≈ pf refl

  ∘-resp-≈ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≈ h → g ∘ f ≈ g ∘ h
  ∘-resp-≈ʳ pf = ∘-resp-≈ refl pf

  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  -- When a category is quantified, it is convenient to refer to the levels from a module,
  -- so we do not have to explicitly quantify over a category when universe levels do not
  -- play a big part in a proof (which is the case probably all the time).
  o-level : Level
  o-level = o

  ℓ-level : Level
  ℓ-level = ℓ

  e-level : Level
  e-level = e

module _ {o ℓ e : Level} where

  -- Convenience functions for working over multiple categories at once:
  -- C [ x , y ] (for x y objects of C) - Hom_C(x , y)
  -- C [ f ≈ g ] (for f g arrows of C)  - that f and g are equivalent arrows
  -- C [ f ∘ g ] (for f g composable arrows of C) - composition in C
  infix 10  _[_,_] _[_≈_] _[_∘_]

  _[_,_] : (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
  _[_,_] = Category._⇒_

  _[_≈_] : (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Prop e
  _[_≈_] = Category._≈_

  _[_∘_] : (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
  _[_∘_] = Category._∘_
