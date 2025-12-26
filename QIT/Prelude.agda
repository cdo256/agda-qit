module QIT.Prelude where

open import Level public using (Level; _⊔_; Lift; lift)
  renaming (suc to lsuc; zero to lzero)
import Relation.Binary.PropositionalEquality
module ≡ = Relation.Binary.PropositionalEquality
open ≡ public using (_≡_; subst) public

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level


-- A wrapper to lift Prop into Set
record Box {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor box
  field unbox : P

open Box

Rel : ∀ (X : Set ℓ) ℓ' → Set (ℓ ⊔ lsuc ℓ')
Rel X ℓ' = X → X → Prop ℓ'

data ∥_∥ (A : Set ℓ) : Prop ℓ where
  ∣_∣ : A → ∥ A ∥

Trunc₁ : {A : Set ℓ} {ℓ' : Level} → (A → Set ℓ') → (A → Prop ℓ')
Trunc₁ R x = ∥ R x ∥

Trunc₂ : {A : Set ℓ} {ℓ' : Level} → (A → A → Set ℓ') → (A → A → Prop ℓ')
Trunc₂ R x y = ∥ R x y ∥

infix 4 _≡p_
_≡p_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Prop ℓ
x ≡p y = ∥ x ≡ y ∥

infix 4 _≡ᴾ_
_≡ᴾ_ : ∀ {ℓ} {A : Prop ℓ} (x y : A) → Set ℓ
x ≡ᴾ y = box x ≡ box y

substp : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
substp B _≡_.refl x = x

substp' : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡p a2) → B a1 → B a2
substp' B ∣ _≡_.refl ∣ x = x

postulate
  -- Cannot be proven from funExt
  funExtp : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → (∀ x → f x ≡p g x) → f ≡p g

open import Axiom.Extensionality.Propositional

postulate
  funExt : ∀ {ℓ ℓ'} → Extensionality ℓ ℓ'

subst-id : {A : Set} {P : A → Set} {x : A} (p : x ≡ x) (b : P x)
         → subst P p b ≡ b
subst-id ≡.refl b = ≡.refl

open import Data.Empty

data ⊥p : Prop where
absurdp : {A : Prop} → ⊥p → A
absurdp ()

⊥→⊥p : ⊥ → ⊥p
⊥→⊥p ()

module ↔ where
  record _↔_ (X Y : Set) : Set where
    field
      to : X → Y
      from : Y → X
      rinv : ∀ x → from (to x) ≡ x
      linv : ∀ y → to (from y) ≡ y

  open _↔_ public

  flip : {X Y : Set} → X ↔ Y → Y ↔ X
  flip X↔Y = record
    { to = X↔Y .from
    ; from = X↔Y .to
    ; rinv = X↔Y .linv
    ; linv = X↔Y .rinv }
    where open _↔_ X↔Y

open ↔ using (_↔_) public

⊥* : ∀ {ℓ} → Set ℓ
⊥* {ℓ} = Lift ℓ ⊥

congp : ∀ {a b} {A : Set a} {B : Prop b} (f : A → B)
      → ∀ {x y} → x ≡ y → f x ≡ᴾ f y
congp f ≡.refl = ≡.refl

congp' : ∀ {a b} {A : Prop a} {B : Set b} (f : A → B)
      → ∀ {x y : A} → x ≡ᴾ y → f x ≡ f y
congp' f ≡.refl = ≡.refl

¬p_ : ∀ {ℓ} (X : Prop ℓ) → Prop ℓ
¬p X = X → ⊥p

¬_ : ∀ {ℓ} (X : Set ℓ) → Set ℓ
¬ X = X → ⊥

record _∧_ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  field
    fst : A
    snd : B

data _∨_ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  inl : A → A ∨ B
  inr : B → A ∨ B

_⇔_ : ∀ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') → Prop (ℓ ⊔ ℓ')
A ⇔ B = (A → B) ∧ (B → A)
