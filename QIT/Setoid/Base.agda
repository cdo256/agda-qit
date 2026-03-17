open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary

-- Define setoids: sets equipped with an equivalence relation.
-- This is the standard mathematical notion of a setoid, where we have
-- a carrier set and an equivalence relation on it.
--
-- Unlike Agda's built-in propositional equality, setoids allow us to
-- work with quotient-like structures where equality is defined by
-- the user (e.g., equivalence classes, extensional function equality,
-- or bisimilarity).
--
-- The key difference from standard library setoids is that we use
-- predicates (Prop) rather than types (Set) for the equivalence
-- relation and its properties. This is consistent with the QIT
-- library's approach to propositions.
module QIT.Setoid.Base where

-- The usual definition of setoid but with _≈_ and isEquivalence being predicates.
--
-- A setoid consists of:
-- - Carrier: the underlying set of elements
-- - _≈_: an equivalence relation on the carrier
-- - isEquivalence: proof that _≈_ satisfies reflexivity, symmetry, and transitivity
record Setoid ℓ ℓ' : Set (lsuc (ℓ ⊔ ℓ')) where
  infix 4 _≈_
  field
    Carrier       : Set ℓ
    _≈_           : BinaryRel Carrier ℓ'
    isEquivalence : IsEquivalence _≈_

  -- Export the equivalence properties (refl, sym, trans) for convenient use
  open IsEquivalence isEquivalence public

-- Convenient syntactic forms so we don't have to open each setoid.
⟨_⟩ : ∀ {ℓ ℓ'} → Setoid ℓ ℓ' → Set ℓ
⟨ S ⟩ = S .Setoid.Carrier

-- Infix notation for the equivalence relation of a setoid.
_[_≈_] : ∀ {ℓ ℓ'} → (S : Setoid ℓ ℓ') → (x y : S .Setoid.Carrier) → Prop _
S [ x ≈ y ] = S .Setoid._≈_ x y

-- Standard chain reasoning syntax for setoid equivalence.
-- This provides Agda's equational reasoning syntax (≈⟨_⟩ and _∎)
-- for setoid equivalence, allowing readable proofs of the form:
--
--   begin
--     x
--       ≈⟨ p ⟩
--     y
--       ≈⟨ q ⟩
--     z ∎
--
-- where p : x ≈ y and q : y ≈ z, yielding a proof of x ≈ z.
module ≈syntax {ℓ ℓ'} {S : Setoid ℓ ℓ'} where
  open Setoid S renaming (Carrier to A)

  infix 1 begin_
  begin_ : ∀ {x y} → x ≈ y → x ≈ y
  begin p = p

  infixr 2 step-≈
  step-≈ : ∀ (x : A) {y z} → y ≈ z → x ≈ y → x ≈ z
  step-≈ _ q p = trans p q
  syntax step-≈ x q p = x ≈⟨ p ⟩ q

  infix 3 _∎
  _∎ : ∀ x → x ≈ x
  x ∎ = refl

-- Construct a setoid using truncated propositional equality.
-- This gives the "discrete" setoid on any type B, where equivalence
-- is just propositional equality (but truncated to a proposition).
_/≡ : ∀ {ℓ} (B : Set ℓ) → Setoid ℓ ℓ
_/≡ B = record
  { Carrier = B
  ; _≈_ = _≡_
  ; isEquivalence = isEquiv-≡ B }

-- If x ≡ y then x ≈ y in any setoid containing them.
≡→≈ : ∀ {ℓ ℓ'} → (A : Setoid ℓ ℓ') → {x y : ⟨ A ⟩} → x ≡ y → A [ x ≈ y ]
≡→≈ A {x} p = ≡.substp (λ ○ → x ≈ ○) p refl
  where open Setoid A

-- Compatibility alias (≡p→≈ is now the same as ≡→≈)
≡p→≈ : ∀ {ℓ ℓ'} → (A : Setoid ℓ ℓ') → {x y : ⟨ A ⟩} → x ≡ y → A [ x ≈ y ]
≡p→≈ = ≡→≈

-- Lift a setoid to higher universe levels.
-- This allows us to transport setoids from lower levels to higher levels,
-- which is needed when working with functors at different universe levels.
LiftSetoid : ∀ {ℓ ℓ'} (ℓl ℓl' : Level) → Setoid ℓ ℓ' → Setoid (ℓ ⊔ ℓl) (ℓ' ⊔ ℓl')
LiftSetoid ℓl ℓl' A = record
  { Carrier = Lift ℓl (Setoid.Carrier A)
  ; _≈_ = λ x y → LiftP ℓl' (Setoid._≈_ A (lower x) (lower y))
  ; isEquivalence = record
    { refl = liftp (Setoid.refl A)
    ; sym = λ (liftp p) → liftp (Setoid.sym A p)
    ; trans = λ (liftp p) (liftp q) → liftp (Setoid.trans A p q)
    }
  }
