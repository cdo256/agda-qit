open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Setoid
open import QIT.Relation.Binary
open import QIT.Category.Strict
open import QIT.Category.Base

module QIT.Category.Discrete where

DiscreteStrCat : ∀ {ℓA} → Set ℓA → StrictCategory ℓA ℓA
DiscreteStrCat A = record
  { Obj = A
  ; _⇒_ = λ x y → Box (x ≡ y)
  ; id = box ≡.refl
  ; _∘_ = λ (box p) (box q) → box (≡.trans q p)
  ; assoc = ≡.isPropBox _ _
  ; sym-assoc = ≡.isPropBox _ _
  ; identityˡ = ≡.isPropBox _ _
  ; identityʳ = ≡.isPropBox _ _
  ; identity² = ≡.isPropBox _ _
  }

DiscreteCat : ∀ {ℓA} → Set ℓA → Category ℓA ℓA ℓA
DiscreteCat A = StrictCategory→Category (DiscreteStrCat A)

⊤Cat : Category ℓ0 ℓ0 ℓ0
⊤Cat = DiscreteCat ⊤

⊥Cat : Category ℓ0 ℓ0 ℓ0
⊥Cat = DiscreteCat ⊥
