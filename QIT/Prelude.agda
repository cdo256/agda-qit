module QIT.Prelude where

open import Level public using (Level; _⊔_; Lift; lift; lower)
  renaming (suc to lsuc; zero to ℓ0)
import Relation.Binary.PropositionalEquality
module ≡ = Relation.Binary.PropositionalEquality
open ≡ public using (_≡_; subst) public
import Data.Empty
module ⊥ = Data.Empty
open ⊥ using (⊥) public

import Data.Product
module × = Data.Product
open × using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂) public

import Data.Sum
module ⊎ = Data.Sum
open ⊎ using (_⊎_; inj₁; inj₂) public

open import Data.Unit public

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

record LiftP {a} ℓ (A : Prop a) : Prop (a ⊔ ℓ) where
  constructor liftp
  field lowerp : A

open LiftP public

-- A wrapper to lift Prop into Set
record Box {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor box
  field unbox : P

open Box

data ∥_∥ (A : Set ℓ) : Prop ℓ where
  ∣_∣ : A → ∥ A ∥

Trunc₁ : {A : Set ℓ} {ℓ' : Level} → (A → Set ℓ') → (A → Prop ℓ')
Trunc₁ R x = ∥ R x ∥

Trunc₂ : {A : Set ℓ} {ℓ' : Level} → (A → A → Set ℓ') → (A → A → Prop ℓ')
Trunc₂ R x y = ∥ R x y ∥

-- These are quite differnet concepts, with confusingly similar names.
-- ≡p is trunctated equality down to a path.
infix 4 _≡p_
_≡p_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Prop ℓ
x ≡p y = ∥ x ≡ y ∥

pattern reflp = ∣ ≡.refl ∣

symp : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡p y → y ≡p x 
symp reflp = reflp

transp : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡p y → y ≡p z → x ≡p z 
transp reflp reflp = reflp

substp : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
substp B ≡.refl x = x

substp' : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡p a2) → B a1 → B a2
substp' B ∣ _≡_.refl ∣ x = x

postulate
  -- Cannot be proven from funExt
  funExt : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
         → (∀ x → f x ≡ g x) → f ≡ g
  funExtp : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
          → (∀ x → f x ≡p g x) → f ≡p g


subst-id : {A : Set} {P : A → Set} {x : A} (p : x ≡ x) (b : P x)
         → subst P p b ≡ b
subst-id ≡.refl b = ≡.refl


data ⊥p : Prop where
absurdp : {A : Prop} → ⊥p → A
absurdp ()

⊥→⊥p : ⊥ → ⊥p
⊥→⊥p ()

-- Bijections
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

absurd* : ∀ {ℓ ℓ'} {A : Set ℓ} → ⊥* {ℓ = ℓ'} → A
absurd* ()

congp : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
      → ∀ {x y} → x ≡p y → f x ≡p f y
congp f ∣ ≡.refl ∣ = ∣ ≡.refl ∣

¬_ : ∀ {ℓ} (X : Prop ℓ) → Prop ℓ
¬ X = X → ⊥p

record _∧_ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B

data _∨_ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  inl : A → A ∨ B
  inr : B → A ∨ B

_⇔_ : ∀ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') → Prop (ℓ ⊔ ℓ')
A ⇔ B = (A → B) ∧ (B → A)

data Dec {ℓA} (A : Set ℓA) : Set ℓA where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

Discrete : ∀ {ℓA} (A : Set ℓA) → Set ℓA
Discrete A = ∀ (x y : A) → Dec (x ≡ y)

infixr 3 if_then_else_
if_then_else_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (decA : Dec A) → B → B → B
if yes _ then b else b' = b
if no _ then b else b' = b'
