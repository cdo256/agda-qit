module QIT.Relation.Nullary where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
import Data.Bool as Bool
open Bool using (Bool; true; false)

-- Decidability type - constructive decision procedures.
data Dec {ℓA} (A : Set ℓA) : Set ℓA where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

-- Decidability type - constructive decision procedures.
data Decᵖ {ℓA} (A : Prop ℓA) : Set ℓA where
  yes : A → Decᵖ A
  no : (A → ⊥p) → Decᵖ A

data True : Bool → Prop where
  true : True true

True? : ∀ b → Decᵖ (True b)
True? false = no (λ ())
True? true = yes true

open import Function.Base using (case_of_; case_returning_of_) public

-- Discrete types - equality is decidable.
Discreteᵖ : ∀ {ℓA} (A : Set ℓA) → Prop ℓA
Discreteᵖ A = ∀ (x y : A) → ∥ Decᵖ (x ≡ y) ∥

-- Discrete types - equality is decidable.
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

const : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (a : A) → B → A
const a _ = a

isProp : ∀ {ℓA} → Set ℓA → Prop ℓA
isProp A = ∀ (x y : A) → x ≡ y

hProp : ∀ ℓA → Set (lsuc ℓA)
hProp ℓA = ΣP (Set ℓA) isProp

hProp→Prop : ∀ {ℓA} → hProp ℓA → Prop ℓA
hProp→Prop (A , _) = ∥ A ∥

Prop→hProp : ∀ {ℓA} → Prop ℓA → hProp ℓA
Prop→hProp A = Box A , ≡.isPropBox

isContr : ∀ {ℓA} → Set ℓA → Prop ℓA
isContr A = ∃ λ (x : A) → ∀ y → x ≡ y

mkIsContr
  : ∀ {ℓA} → (A : Set ℓA)
  → ∥ A ∥ → isProp A → isContr A
mkIsContr A ∣ x ∣ isPropA = ∣ x , isPropA x ∣

Σ≡Prop
  : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
  → ((x : A) → isProp (B x)) → {u v : Σ A B}
  → (p : u .proj₁ ≡ v .proj₁) → u ≡ v
Σ≡Prop pB {x , u} {x , v} ≡.refl =
  ≡.cong (x ,_) (pB x u v)

isSetSet : ∀ {ℓA} {A : Set ℓA} {x y : A} (p q : x ≡ y) → p ≡ᵖ q
isSetSet ≡.refl ≡.refl = ≡.refl

postulate
  A!C : ∀ {ℓX} (X : Set ℓX) → isContr X → X

