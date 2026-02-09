open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Relation.Binary
open import QIT.Category.Base

module QIT.Category.Set where

SetCat : ∀ ℓA → Category (lsuc ℓA) (ℓA) ℓA
SetCat ℓA = record
  { Obj = Set ℓA
  ; _⇒_ = λ X Y → (X → Y)
  ; _≈_ = _≡p_
  ; id = λ x → x
  ; _∘_ = _∘_
  ; assoc = reflp
  ; sym-assoc = reflp
  ; identityˡ = reflp
  ; identityʳ = reflp
  ; identity² = reflp
  ; equiv = λ {A B} → isEquiv-≡p (A → B)
  ; ∘-resp-≈ = λ{ reflp reflp → reflp }
  }
