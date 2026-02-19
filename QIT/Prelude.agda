module QIT.Prelude where

-- Foundational definitions and type theory concepts for the QIT development.
-- Provides constructive foundations without choice principles, careful universe
-- level management, and propositional truncation for proof-irrelevant statements.

-- Universe level management - crucial for building large type constructions.
open import Level public using (Level; _⊔_; Lift; lift; lower)
  renaming (suc to lsuc; zero to ℓ0)

-- Propositional equality - the basic definitional equality in Agda.
import Relation.Binary.PropositionalEquality
module ≡ = Relation.Binary.PropositionalEquality
open ≡ public using (_≡_; subst) public

import Relation.Binary.HeterogeneousEquality 
module ≣ = Relation.Binary.HeterogeneousEquality 
open ≣ public using () renaming (_≅_ to _≣_)

-- Empty type - represents logical falsehood and impossible cases.
import Data.Empty
module ⊥ = Data.Empty
open ⊥ using (⊥) public

-- Product types - both dependent (Σ) and non-dependent (_×_).
import Data.Product
module × = Data.Product
open × using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂) public

import Agda.Builtin.Sigma
{-# DISPLAY Agda.Builtin.Sigma.Σ.fst = proj₁ #-}
{-# DISPLAY Agda.Builtin.Sigma.Σ.snd = proj₂ #-}

-- Sum types - represents disjoint union and logical disjunction.
import Data.Sum
module ⊎ = Data.Sum
open ⊎ using (_⊎_; inj₁; inj₂) public

open import Data.Unit public

postulate
  -- Function extensionality: if functions are pointwise equal, they are equal.
  -- Cannot be proven in basic Agda but is consistent and often needed.
  funExt : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
         → (∀ x → f x ≡ g x) → f ≡ g

-- Coherence law for substitution with reflexivity.
subst-id : {A : Set} {P : A → Set} {x : A} (p : x ≡ x) (b : P x)
         → subst P p b ≡ b
subst-id ≡.refl b = ≡.refl

-- Bijections between sets - one-to-one correspondences with explicit inverses.
module ↔ where
  record _↔_ (X Y : Set) : Set where
    field
      to : X → Y
      from : Y → X
      rinv : ∀ x → from (to x) ≡ x
      linv : ∀ y → to (from y) ≡ y

  open _↔_ public

  refl : {X : Set} → X ↔ X
  refl = record
    { to = λ x → x
    ; from = λ x → x
    ; rinv = λ _ → ≡.refl
    ; linv = λ _ → ≡.refl }

  flip : {X Y : Set} → X ↔ Y → Y ↔ X
  flip X↔Y = record
    { to = X↔Y .from
    ; from = X↔Y .to
    ; rinv = X↔Y .linv
    ; linv = X↔Y .rinv }
    where open _↔_ X↔Y

  _∘_ : {X Y Z : Set} → Y ↔ Z → X ↔ Y → X ↔ Z
  q ∘ p = record
    { to = λ x → q.to (p.to x)
    ; from = λ z → p.from (q.from z)
    ; rinv = λ x → ≡.trans (≡.cong p.from (q.rinv (p.to x))) (p.rinv x)
    ; linv = λ z → ≡.trans (≡.cong q.to (p.linv (q.from z))) (q.linv z) }
    where
    module p = _↔_ p
    module q = _↔_ q

open ↔ using (_↔_) public

-- Empty type at arbitrary universe levels.
⊥* : ∀ {ℓ} → Set ℓ
⊥* {ℓ} = Lift ℓ ⊥

absurd* : ∀ {ℓ ℓ'} {A : Set ℓ} → ⊥* {ℓ = ℓ'} → A
absurd* ()

-- Decidability type - constructive decision procedures.
data Dec {ℓA} (A : Set ℓA) : Set ℓA where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

-- Discrete types - equality is decidable.
Discrete : ∀ {ℓA} (A : Set ℓA) → Set ℓA
Discrete A = ∀ (x y : A) → Dec (x ≡ y)

-- Conditional expression based on decidability.
infixr 3 if_then_else_
if_then_else_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (decA : Dec A) → B → B → B
if yes _ then b else b' = b
if no _ then b else b' = b'

const : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (a : A) → B → A
const a _ = a

isProp : ∀ {ℓA} → Set ℓA → Set ℓA
isProp A = ∀ (x y : A) → x ≡ y

isContr : ∀ {ℓA} → Set ℓA → Set ℓA
isContr A = Σ A λ x → ∀ y → x ≡ y

≡cong₃ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {D : Set ℓD}
      → (f : A → B → C → D) → ∀ {u v w x y z} → u ≡ v → w ≡ x → y ≡ z → f u w y ≡ f v x z
≡cong₃ f ≡.refl ≡.refl ≡.refl = ≡.refl

≡subst₃ : ∀ {ℓA ℓB ℓC ℓR} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
        → (R : A → B → C → Set ℓR) → ∀ {u v w x y z} → u ≡ v → w ≡ x → y ≡ z → R u w y → R v x z
≡subst₃ f ≡.refl ≡.refl ≡.refl a = a
