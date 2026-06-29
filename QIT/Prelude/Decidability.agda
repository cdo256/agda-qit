module QIT.Prelude.Decidability where

open import QIT.Prelude.Universe
open import QIT.Prelude.Types
open import QIT.Prelude.Truncation
open import QIT.Prelude.Identity
open import QIT.Prelude.Logic

data Dec (A : Set ℓA) : Set ℓA where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

data Decᵖ (A : Prop ℓA) : Set ℓA where
  yes : A → Decᵖ A
  no : (A → ⊥) → Decᵖ A

data True : Bool → Prop where
  true : True true

True? : ∀ b → Decᵖ (True b)
True? false = no (λ ())
True? true = yes true

case_returning_of_
  : {A : Set ℓA} (x : A) (B : A → Set ℓB)
  → ((x : A) → B x) → B x
case x returning B of f = f x
{-# INLINE case_returning_of_ #-}

case_of_ : {A : Set ℓA} {B : Set ℓB} → A → (A → B) → B
case a of f = f a
{-# INLINE case_of_ #-}

Discrete : (A : Set ℓA) → Set ℓA
Discrete A = ∀ (x y : A) → Decᵖ (x ≡ y)

-- Conditional expression based on decidability.
infixr 3 if_then_else_
if_then_else_
  : {A : Set ℓA} {B : Set ℓB}
  → (decA : Dec A) → B → B → B
if yes _ then b else b' = b
if no _ then b else b' = b'

-- Conditional expression based on decidability.
infixr 3 ifᵖ_then_else_
ifᵖ_then_else_
  : {A : Prop ℓA} {B : Set ℓB}
  → (decA : Decᵖ A) → B → B → B
ifᵖ yes _ then b else b' = b
ifᵖ no _ then b else b' = b'
