open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Setoid
open import QIT.Relation.Binary
open import QIT.Category.Base
open import QIT.Category.SetoidEnriched

module QIT.Category.Discrete where

DiscreteCat≈ : ∀ {ℓA ℓA≈} → Setoid ℓA ℓA≈
             → Category≈ ℓA ℓA≈ ℓA≈ ℓ0
DiscreteCat≈ Ã = record
  { Obj = A
  ; _≈⁰_ = _≈_
  ; _⇒_ = λ x y → Box (x ≈ y)
  -- we only have identity arrows, so any pair of arrows between the
  -- same pair of objects must be equal. In other words, in a discrete
  -- category, all hom-sets are propositional.
  ; _≈⃗_ = λ _ _ → ∥ ⊤ ∥
  ; id = box refl
  ; _∘_ = λ p q → box (trans (unbox q) (unbox p))
  ; equiv⁰ = isEquivalence
  ; equiv⃗ = record
    { refl = ∣ tt ∣
    ; sym = λ _ → ∣ tt ∣
    ; trans = λ _ _ → ∣ tt ∣ }
  ; subst⁰ = λ A≈B C≈D A≈Cᵇ → box (trans (sym A≈B) (trans (unbox A≈Cᵇ) C≈D))
  ; subst-resp-≈⃗ = λ _ _ _ → ∣ tt ∣
  ; subst-refl = ∣ tt ∣
  ; subst-trans = λ _ _ _ _ _ → ∣ tt ∣
  ; assoc = ∣ tt ∣
  ; sym-assoc = ∣ tt ∣
  ; identityˡ = ∣ tt ∣
  ; identityʳ = ∣ tt ∣
  ; identity² = ∣ tt ∣
  ; ∘-resp-≈ = λ _ _ → ∣ tt ∣
  ; subst-id⁰ = λ _ → ∣ tt ∣
  ; subst-∘ = λ _ _ _ _ _ → ∣ tt ∣
  }
  where open Setoid Ã renaming (Carrier to A)

DiscreteCat : ∀ {ℓA} → Set ℓA → Category ℓA ℓA ℓA
DiscreteCat A = record
  { Obj = A
  ; _⇒_ = _≡_
  ; _≈_ = _≡_
  ; id = ≡.refl
  ; _∘_ = λ p q → ≡.trans q p
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = λ {a b} → isEquiv-≡ (a ≡ b)
  ; ∘-resp-≈ = λ{ ≡.refl ≡.refl → ≡.refl }
  }

⊤Cat : Category ℓ0 ℓ0 ℓ0
⊤Cat = DiscreteCat ⊤

⊥Cat : Category ℓ0 ℓ0 ℓ0
⊥Cat = DiscreteCat ⊥
