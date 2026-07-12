open import QIT.Prelude

module QIT.Examples.PartialityMonad.QW ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prelude.Logic renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Nat as ℕ

interleaved mutual
  infix 4 _≤_ _≈_
  data A⊥ : Set
  data _≤_ : A⊥ → A⊥ → Set
  data _≈_ : A⊥ → A⊥ → Set

  data _ where
    η : Bool → A⊥
    ⊥ : A⊥
    ⨆ : (a : ℕ → A⊥) (a-inc : ∀ i → a i ≤ a (suc i)) → A⊥
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ⊥≤ : ∀ {x} → ⊥ ≤ x
    ≤⨆ : ∀ a a-inc i → a i ≤ ⨆ a a-inc
    ⨆≤ : ∀ a a-inc x → (∀ i → a i ≤ x) → ⨆ a a-inc ≤ x
    ≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

record Algebra : Set₁ where
  infix 4 _≤ᴬ_

  field
    A⊥ᴬ : Set
    _≤ᴬ_ : A⊥ᴬ → A⊥ᴬ → Set

    ηᴬ : Bool → A⊥ᴬ
    ⊥ᴬ : A⊥ᴬ
    ⨆ᴬ : (a : ℕ → A⊥ᴬ) → (a-inc : ∀ i → a i ≤ᴬ a (suc i)) → A⊥ᴬ
    ≤reflᴬ : ∀ {x} → x ≤ᴬ x
    ≤transᴬ : ∀ {x y z} → x ≤ᴬ y → y ≤ᴬ z → x ≤ᴬ z
    ⊥≤ᴬ : ∀ {x} → ⊥ᴬ ≤ᴬ x
    ≤⨆ᴬ : ∀ a a-inc i → a i ≤ᴬ ⨆ᴬ a a-inc
    ⨆≤ᴬ : ∀ a a-inc x → (∀ i → a i ≤ᴬ x) → ⨆ᴬ a a-inc ≤ᴬ x
    antisymᴬ : ∀ {x y} → x ≤ᴬ y → y ≤ᴬ x → x ≡ y
  
data S : Set where
  ηˢ : Bool → S
  ⊔ˢ : S
  ⨆ˢ : S
  junkˢ : S

data P : S → Set where
  ⊔ˢ-l : P ⊔ˢ
  ⊔ˢ-r : P ⊔ˢ
  ⊔ᵖ : ℕ → P ⨆ˢ

-- data E : Set where
--   asᵉ : E
-- 
-- data V : E → Set where
--   w : ℕ → V asᵉ

open import QIT.QW.Signature
open import QIT.QW.W
open import QIT.Container.Base
open import QIT.QW.Equation S P ℓ0

data E : Set where
  excludeᴱ : ℕ → ℕ → E
  cofinalᴱ : ℕ → ℕ → E

Ξ : E → Equation
Ξ (excludeᴱ i j) =
  record
  { V = ℕ
  ; lhs = supᴱ ⨆ˢ (vl i j)
  ; rhs = {!!} }
  where
  open import QIT.Fin.Base
  open import QIT.Relation.Nullary
  vl : ℕ → ℕ → Pʰ ℕ (inj₂ ⨆ˢ) → Expr ℕ
  vl i j (⊔ᵖ k) with k ≟ℕ i | k ≟ℕ j
  ... | yes p | yes q = {!!}
  ... | yes p | no ¬q = {!!}
  ... | no ¬p | yes q = {!!}
  ... | no ¬p | no ¬q = {!!}


Ξ (cofinalᴱ i j) =
  record
  { V = {!!}
  ; lhs = {!!}
  ; rhs = {!!} }

