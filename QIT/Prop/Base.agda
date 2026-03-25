open import QIT.Prelude

module QIT.Prop.Base where

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

-- Lift propositions to higher universe levels.
record LiftP {a} ℓ (A : Prop a) : Prop (a ⊔ ℓ) where
  constructor liftp
  field lowerp : A

open LiftP public

-- Wrapper to lift Prop into Set when needed.
record Box {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor box
  field unbox : P

open Box public

-- Propositional truncation: makes types proof-irrelevant.
-- ∥ A ∥ says "there exists an element of A, but we don't care which one".
-- Enables constructive existence proofs without violating computational content.
data ∥_∥ (A : Set ℓ) : Prop ℓ where
  ∣_∣ : A → ∥ A ∥

-- Truncated unary relations - convert relations to proof-irrelevant versions.
Trunc₁ : {A : Set ℓ} {ℓ' : Level} → (A → Set ℓ') → (A → Prop ℓ')
Trunc₁ R x = ∥ R x ∥

-- Truncated binary relations - essential for setoid equality relations.
Trunc₂ : {A : Set ℓ} {ℓ' : Level} → (A → A → Set ℓ') → (A → A → Prop ℓ')
Trunc₂ R x y = ∥ R x y ∥
