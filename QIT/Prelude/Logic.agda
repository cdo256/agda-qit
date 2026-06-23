open import QIT.Prelude.Universe
open import QIT.Prelude.Types
open import QIT.Prelude.Truncation

module QIT.Prelude.Logic where

data ⊥ : Prop where
⊥* : Prop ℓA
⊥* = LiftP _ ⊥

data ⊤ : Prop where
  tt : ⊤
⊤* : Prop ℓA
⊤* = LiftP _ ⊤

pattern tt* = liftp tt

infix 6 ¬_
¬_ : Prop ℓA → Prop ℓA
¬ X = X → ⊥

infixr 2 _∧ᵖ_
infixr 2 _∧_
record _∧ᵖ_ (A : Prop ℓA) (B : A → Prop ℓB) : Prop (ℓA ⊔ ℓB) where
  constructor ∧i
  field
    ∧e₁ : A
    ∧e₂ : B ∧e₁
open _∧ᵖ_ public

_∧_ : (A : Prop ℓA) (B : Prop ℓB) → Prop (ℓA ⊔ ℓB) 
A ∧ B = A ∧ᵖ λ _ → B

infixr 1 _∨_
data _∨_ (A : Prop ℓA) (B : Prop ℓB) : Prop (ℓA ⊔ ℓB) where
  ∨i₁ : A → A ∨ B
  ∨i₂ : B → A ∨ B

∨e : {A : Prop ℓA} {B : Prop ℓB} {C : Prop ℓC}
   → (A → C) → (B → C) → (A ∨ B) → C
∨e f g (∨i₁ a) = f a
∨e f g (∨i₂ b) = g b

-- Bi-implication for propositions.
infix 1 _⇔_
_⇔_ : (A : Prop ℓA) (B : Prop ℓB) → Prop (ℓA ⊔ ℓB)
A ⇔ B = (A → B) ∧ (B → A)

data ∃ {A : Set ℓA} (B : A → Prop ℓB) : Prop (ℓA ⊔ ℓB) where
  ∃i : (a : A) → (b : B a) → ∃ B

∃e : {A : Set ℓA} {B : A → Prop ℓB} {C : Prop ℓC}
   → (∀ a → B a → C) → ∃ B → C
∃e f (∃i a b) = f a b
