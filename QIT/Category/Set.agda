open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Relation.Binary
open import QIT.Category.Base
open import QIT.Category.Strict

module QIT.Category.Set where

SetStrCat : ∀ ℓA → StrictCategory (lsuc ℓA) ℓA
SetStrCat ℓA = record
  { Obj = Set ℓA
  ; _⇒_ = λ X Y → (X → Y)
  ; id = λ x → x
  ; _∘_ = _∘_
  ; assoc = ≡.refl
  ; sym-assoc = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; identity² = ≡.refl
  }

SetCat : ∀ ℓA → Category (lsuc ℓA) ℓA ℓA
SetCat ℓA = StrictCategory→Category (SetStrCat ℓA)
