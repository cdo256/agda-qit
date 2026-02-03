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

-- Empty type - represents logical falsehood and impossible cases.
import Data.Empty
module ⊥ = Data.Empty
open ⊥ using (⊥) public

-- Product types - both dependent (Σ) and non-dependent (_×_).
import Data.Product
module × = Data.Product
open × using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂) public

-- Sum types - represents disjoint union and logical disjunction.
import Data.Sum
module ⊎ = Data.Sum
open ⊎ using (_⊎_; inj₁; inj₂) public

open import Data.Unit public

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
  -- Function extensionality: if functions are pointwise equal, they are equal.
  -- Cannot be proven in basic Agda but is consistent and often needed.
  funExt : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
         → (∀ x → f x ≡ g x) → f ≡ g

  -- Truncated function extensionality.
  funExtp : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
          → (∀ x → f x ≡p g x) → f ≡p g

-- Coherence law for substitution with reflexivity.
subst-id : {A : Set} {P : A → Set} {x : A} (p : x ≡ x) (b : P x)
         → subst P p b ≡ b
subst-id ≡.refl b = ≡.refl

-- Propositional empty type - logical contradiction at the propositional level.
data ⊥p : Prop where

-- Explosion principle for propositions.
absurdp : {A : Prop} → ⊥p → A
absurdp ()

-- Convert Set-level falsity to propositional falsity.
⊥→⊥p : ⊥ → ⊥p
⊥→⊥p ()

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
