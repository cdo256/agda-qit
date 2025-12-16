module Prelude where

open import Level public using (Level; _⊔_; Lift; lift)
  renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_) public

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level


-- A wrapper to lift Prop into Set
record Box {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor box
  field unbox : P

open Box

substp : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
substp B _≡_.refl x = x

Rel : ∀ (X : Set ℓ) ℓ' → Set (ℓ ⊔ lsuc ℓ')
Rel X ℓ' = X → X → Prop ℓ'

data ∥_∥ (A : Set ℓ) : Prop ℓ where
  ∣_∣ : A → ∥ A ∥

Trunc₁ : {A : Set ℓ} {ℓ' : Level} → (A → Set ℓ') → (A → Prop ℓ')
Trunc₁ R x = ∥ R x ∥

Trunc₂ : {A : Set ℓ} {ℓ' : Level} → (A → A → Set ℓ') → (A → A → Prop ℓ')
Trunc₂ R x y = ∥ R x y ∥
