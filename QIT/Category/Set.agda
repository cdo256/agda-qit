open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Relation.Binary
open import QIT.Category.Base

module QIT.Category.Set where

open _≡_

SetCat : ∀ ℓA → Category (lsuc ℓA) (ℓA) ℓA
SetCat ℓA = record
  { Obj = Set ℓA
  ; _⇒_ = λ X Y → (X → Y)
  ; _≈_ = _≡_
  ; id = λ x → x
  ; _∘_ = _∘_
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = λ {A B} → isEquiv-≡ (A → B)
  ; ∘-resp-≈ = λ{ ≡.refl ≡.refl → ≡.refl }
  }
