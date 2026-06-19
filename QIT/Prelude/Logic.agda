open import QIT.Prelude.Universe
open import QIT.Prelude.Types
open import QIT.Prelude.Identity
open import QIT.Prelude.Truncation

module QIT.Prelude.Logic where

infix 6 ¬_
¬_ : ∀ {ℓ} (X : Prop ℓ) → Prop ℓ
¬ X = X → ⊥p

module ∧ {ℓ ℓ'} where
  infixr 2 _∧ᵖ_
  infixr 2 _∧_
  infixr 4 _,_
  record _∧ᵖ_ (A : Prop ℓ) (B : A → Prop ℓ') : Prop (ℓ ⊔ ℓ') where
    constructor _,_
    field
      fst : A
      snd : B fst
  open _∧ᵖ_ public

  _∧_ : (A : Prop ℓ) (B : Prop ℓ') → Prop (ℓ ⊔ ℓ') 
  A ∧ B = A ∧ᵖ λ _ → B

open ∧ public using (_∧ᵖ_; _∧_; _,_)

module ∨ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') where
  infixr 1 _∨_
  data _∨_ : Prop (ℓ ⊔ ℓ') where
    inl : A → _∨_
    inr : B → _∨_

open ∨ public using (_∨_)

-- Bi-implication for propositions.
infix 1 _⇔_
_⇔_ : ∀ {ℓA ℓB} (A : Prop ℓA) (B : Prop ℓB) → Prop (ℓA ⊔ ℓB)
A ⇔ B = (A → B) ∧ (B → A)

∃ : ∀ {a b} {A : Set a} → (A → Prop b) → Prop (a ⊔ b)
∃ {A = A} B = ∥ ΣP A B ∥
