{-# OPTIONS --type-in-type #-}
module QIT.Setoid.Indexed where

open import QIT.Prelude
open import Data.Product
open import QIT.Relation.Base
import QIT.Relation.IndexedBinary as IndexedBinary


record Setoid ℓI ℓA ℓR : Set (lsuc (ℓI ⊔ ℓA ⊔ ℓR)) where
  field
    I             : Set ℓI
    A             : I → Set ℓA
    R             : IndexedBinaryRel A ℓR
    isEquivalence : IndexedBinary.IsEquivalence A R

  open IndexedBinary.IsEquivalence isEquivalence public

module _ {ℓI ℓA ℓR} (S : Setoid ℓI ℓA ℓR) where
  open Setoid S

  ⟨_⟩ : (S .Setoid.I → Set ℓA)
  ⟨_⟩ = A

  _[_≈_] : ∀ {i j} → A i → A j → Prop _
  _[_≈_] {i} {j} x y = R i j x y

  infix 4 _≈_
  _≈_ : ∀ {i j} → A i → A j → Prop _
  _≈_ {i} {j} x y = R i j x y

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

  open import Data.Unit

  UnindexedSetoid→IndexedSetoid : ∀ {ℓA ℓR} → Unindexed.Setoid ℓA ℓR → Setoid lzero ℓA ℓR
  UnindexedSetoid→IndexedSetoid S = record
      { I = ⊤
      ; A = λ _ → S.Carrier
      ; R = λ _ _ x y → x S.≈ y
      ; isEquivalence = record
        { refl = S.refl
        ; sym = S.sym
        ; trans = S.trans } }
    where module S = Unindexed.Setoid S
