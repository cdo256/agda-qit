open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid.Base
open import QIT.Setoid.Hom

module QIT.Setoid.Exponential where

_⇨_ : ∀ {ℓA ℓA' ℓB ℓB'} → Setoid ℓA ℓA' → Setoid ℓB ℓB'
    → Setoid {!!} {!!}
A ⇨ B = record
  { Carrier = Hom A B
  ; _≈_ = _≈h_
  ; isEquivalence = {!!} }

