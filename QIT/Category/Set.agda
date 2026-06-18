open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Relation.Binary
open import QIT.Category.Base
open import QIT.Category.Strict

module QIT.Category.Set where

SetCat : ∀ ℓA → Category (lsuc ℓA) ℓA ℓA
SetCat ℓA = record
  { Obj = Set ℓA
  ; _⇒_ = λ X Y → (X → Y)
  ; id = λ x → x
  ; _∘_ = _∘_
  ; assoc = reflˢ
  ; sym-assoc = reflˢ
  ; identityˡ = reflˢ
  ; identityʳ = reflˢ
  ; identity² = reflˢ
  ; _≈_ = _≡hˢ_
  ; equiv = isEquiv-≡hˢ
  ; ∘-resp-≈ = ∘-resp-≡hˢ
  }
