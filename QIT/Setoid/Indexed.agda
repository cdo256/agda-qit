module QIT.Setoid.Indexed where

open import QIT.Prelude
open import QIT.Relation.Base
import QIT.Relation.IndexedBinary as IndexedBinary

-- Indexed setoids generalize ordinary setoids by allowing the carrier to vary
-- over an index set. This is crucial for the QIT development where we need to
-- relate elements living at different stages or levels of a construction.

record Setoid ℓI ℓA ℓR : Set (lsuc (ℓI ⊔ ℓA ⊔ ℓR)) where
  field
    I             : Set ℓI
    A             : I → Set ℓA
    R             : IndexedBinaryRel A ℓR
    isEquivalence : IndexedBinary.IsEquivalence A R

  open IndexedBinary.IsEquivalence isEquivalence public

  infix 4 _≈_
  _≈_ : ∀ {i j} → A i → A j → Prop _
  _≈_ {i} {j} x y = R i j x y


module _ {ℓI ℓA ℓR} (S : Setoid ℓI ℓA ℓR) where
  open Setoid S

  ⟨_⟩ : (S .Setoid.I → Set ℓA)
  ⟨_⟩ = A

  _[_≈_] : ∀ {i j} → A i → A j → Prop _
  _[_≈_] {i} {j} x y = R i j x y

  -- Equational reasoning syntax for indexed setoids.
  -- Allows writing proofs in chain style: begin x ≈⟨ p ⟩ y ≈⟨ q ⟩ z ∎
  -- Transitivity can involve three different indices i, j, k.
  module ≈syntax where
    infix 1 begin_
    begin_ : ∀ {i j} {x : A i} {y : A j} → x ≈ y → x ≈ y
    begin p = p

    infixr 2 step-≈
    step-≈ : ∀ {i j k} (x : A i) {y : A j} {z : A k} → y ≈ z → x ≈ y → x ≈ z
    step-≈ _ q p = trans p q
    syntax step-≈ x q p = x ≈⟨ p ⟩ q

    infix 3 _∎
    _∎ : ∀ {i} (x : A i) → x ≈ x
    x ∎ = refl

module _ where
  import QIT.Setoid.Base as Unindexed

  -- Convert a regular setoid to an indexed setoid with trivial indexing.
  -- Uses the unit type ⊤ as the index set, so there's only one index.
  UnindexedSetoid→IndexedSetoid : ∀ {ℓA ℓR} → Unindexed.Setoid ℓA ℓR → Setoid ℓ0 ℓA ℓR
  UnindexedSetoid→IndexedSetoid S = record
      { I = ⊤ˢ
      ; A = λ _ → S.Carrier
      ; R = λ _ _ x y → x S.≈ y
      ; isEquivalence = record
        { refl = S.refl
        ; sym = S.sym
        ; trans = S.trans } }
    where module S = Unindexed.Setoid S

  -- Convert an indexed setoid (at level ℓ0) to a regular setoid.
  -- Takes the dependent sum Σ I A as the carrier, and defines equality
  -- on pairs (i, x) and (j, y) using the indexed relation R i j x y.
  IndexedSetoid→UnindexedSetoid : ∀ {ℓA ℓR} → Setoid ℓ0 ℓA ℓR → Unindexed.Setoid ℓA ℓR
  IndexedSetoid→UnindexedSetoid S = record
    { Carrier = Σ S.I S.A
    ; _≈_ = λ (i , x) (j , y) → S.R i j x y
    ; isEquivalence = record
      { refl = S.refl
      ; sym = S.sym
      ; trans = S.trans } }
    where module S = Setoid S
