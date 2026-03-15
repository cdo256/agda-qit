open import QIT.Prelude

module QIT.Prop.Unannotated where

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

infix 4 _≡_
data _≡_ {ℓ} {A : Set ℓ} : (x y : A) → Prop ℓ where
  refl : ∀ {x} → x ≡ x

symp : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
symp refl = refl

transp : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transp refl refl = refl


-- Substitution into propositions along propositional equality.
postulate
  substp : ∀ {A : Set ℓ} (B : A → Set ℓ') {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
  substp-id : {A : Set} {P : A → Set} {x : A} (p : x ≡ x) (b : P x)
          → substp P p b ≡ b

-- Binary substitution into propositions.
substp₂ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Prop ℓC) {a1 a2 : A} {b1 b2 : B}
        → (p : a1 ≡ a2) (q : b1 ≡ b2) → C a1 b1 → C a2 b2
substp₂ C refl refl c = c

-- Substitution along truncated equality.
substp' : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
substp' B refl x = x

postulate
  -- Truncated function extensionality.
  funExtp : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
          → (∀ x → f x ≡ g x) → f ≡ g

-- Propositional empty type - logical contradiction at the propositional level.
data ⊥p : Prop where

-- Explosion principle for propositions.
absurdp : {A : Prop} → ⊥p → A
absurdp ()

-- Convert Set-level falsity to propositional falsity.
⊥→⊥p : ⊥ → ⊥p
⊥→⊥p ()

-- Congruence for truncated equality.
congp : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
      → ∀ {x y} → x ≡ y → f x ≡ f y
congp f refl = refl

-- Logical negation for propositions.
infix 6 ¬_
¬_ : ∀ {ℓ} (X : Prop ℓ) → Prop ℓ
¬ X = X → ⊥p

_≢p_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Prop ℓ
x ≢p y = ¬ (x ≡ y)

-- Conjunction for propositions.
module ∧ {ℓ ℓ'} where
  infixr 5 _∧ᵖ_
  infixr 5 _∧_
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

-- Disjunction for propositions.
module ∨ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') where
  infixr 4 _∨_
  data _∨_ : Prop (ℓ ⊔ ℓ') where
    inl : A → _∨_
    inr : B → _∨_

open ∨ public using (_∨_)

-- Bi-implication for propositions.
infix 3 _⇔_
_⇔_ : ∀ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') → Prop (ℓ ⊔ ℓ')
A ⇔ B = (A → B) ∧ (B → A)

