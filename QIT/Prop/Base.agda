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

open Box

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

-- Truncated propositional equality - proof-irrelevant version of ≡.
-- Used when we need equality as a proposition rather than data.
infix 4 _≡p_
_≡p_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Prop ℓ
x ≡p y = ∥ x ≡ y ∥

pattern reflp = ∣ ≡.refl ∣

symp : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡p y → y ≡p x
symp reflp = reflp

transp : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡p y → y ≡p z → x ≡p z
transp reflp reflp = reflp

-- Substitution into propositions along propositional equality.
substp : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
substp B ≡.refl x = x

-- Binary substitution into propositions.
substp₂ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Prop ℓC) {a1 a2 : A} {b1 b2 : B}
        → (p : a1 ≡ a2) (q : b1 ≡ b2) → C a1 b1 → C a2 b2
substp₂ C ≡.refl ≡.refl c = c

-- Substitution along truncated equality.
substp' : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡p a2) → B a1 → B a2
substp' B reflp x = x

postulate
  -- Truncated function extensionality.
  funExtp : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
          → (∀ x → f x ≡p g x) → f ≡p g

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
      → ∀ {x y} → x ≡p y → f x ≡p f y
congp f reflp = reflp

-- Logical negation for propositions.
infix 6 ¬_
¬_ : ∀ {ℓ} (X : Prop ℓ) → Prop ℓ
¬ X = X → ⊥p

-- Conjunction for propositions.
module ∧ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') where
  infixr 5 _∧_
  infixr 4 _,_
  record _∧_ : Prop (ℓ ⊔ ℓ') where
    constructor _,_
    field
      fst : A
      snd : B
  open _∧_ public

open ∧ public using (_∧_; _,_)

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
