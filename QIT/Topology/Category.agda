module QIT.Topology.Category where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Topology.Subset
open import QIT.Topology.Base
open import QIT.Category.Base

module _ {ℓ𝓤 ℓ𝓟 ℓ𝓞} where

  id : (A : Space ℓ𝓤 ℓ𝓟 ℓ𝓞) → A ⇒ A
  id A = (λ z → z) , (λ _ z → z)

  _∘_
    : {A B C : Space ℓ𝓤 ℓ𝓟 ℓ𝓞}
    → (g : B ⇒ C) (f : A ⇒ B)
    → A ⇒ C
  (g , g𝓞) ∘ (f , f𝓞) = record
    { f  = λ x → g (f x)
    ; f𝓞 = λ Z Zopen → f𝓞 (λ y → Z (g y)) (g𝓞 Z Zopen)
    }

Top : ∀ ℓ𝓤 ℓ𝓟 ℓ𝓞 → Category _ _ _
Top ℓ𝓤 ℓ𝓟 ℓ𝓞 = record
  { Obj       = Space ℓ𝓤 ℓ𝓟 ℓ𝓞
  ; _⇒_       = _⇒_
  ; _≈_       = _≡_
  ; id        = id _
  ; _∘_       = _∘_
  ; assoc     = ≡.refl
  ; sym-assoc = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; identity² = ≡.refl
  ; equiv     = isEquiv-≡ _
  ; ∘-resp-≈  = ≡.cong₂ _∘_
  }
