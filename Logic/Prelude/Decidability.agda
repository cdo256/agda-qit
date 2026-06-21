module Logic.Prelude.Decidability where

open import Logic.Prelude.Universe
open import Logic.Prelude.Types
open import Logic.Prelude.Truncation
open import Logic.Prelude.Identity
-- open import Logic.Prop
-- open import Logic.Relation.Base
-- open import Logic.Relation.Subset
-- import Data.Bool as Bool
-- open Bool using (Bool; true; false)

data Dec {ℓA} (A : Set ℓA) : Set ℓA where
  yes : A → Dec A
  no : (A → ⊥p) → Dec A

data Decᵖ {ℓA} (A : Prop ℓA) : Set ℓA where
  yes : A → Decᵖ A
  no : (A → ⊥p) → Decᵖ A

data True : Bool → Prop where
  true : True true

True? : ∀ b → Decᵖ (True b)
True? false = no (λ ())
True? true = yes true

case_returning_of_
  : ∀ {ℓA ℓB} {A : Set ℓA} (x : A) (B : A → Set ℓB)
  → ((x : A) → B x) → B x
case x returning B of f = f x
{-# INLINE case_returning_of_ #-}

case_of_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → A → (A → B) → B
case a of f = f a
{-# INLINE case_of_ #-}

Discreteᵖ : ∀ {ℓA} (A : Set ℓA) → Prop ℓA
Discreteᵖ A = ∀ (x y : A) → ∥ Decᵖ (x ≡ y) ∥

Discrete : ∀ {ℓA} (A : Set ℓA) → Set ℓA
Discrete A = ∀ (x y : A) → Decᵖ (x ≡ y)

-- Conditional expression based on decidability.
infixr 3 if_then_else_
if_then_else_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (decA : Dec A) → B → B → B
if yes _ then b else b' = b
if no _ then b else b' = b'

-- Conditional expression based on decidability.
infixr 3 ifᵖ_then_else_
ifᵖ_then_else_ : ∀ {ℓA ℓB} {A : Prop ℓA} {B : Set ℓB} (decA : Decᵖ A) → B → B → B
ifᵖ yes _ then b else b' = b
ifᵖ no _ then b else b' = b'

