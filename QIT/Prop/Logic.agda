open import QIT.Prelude
open import QIT.Prop.Base
open import QIT.Prop.Path

module QIT.Prop.Logic where

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

data ⊥p : Prop where

⊥p* : ∀ {ℓ} → Prop ℓ
⊥p* {ℓ} = LiftP ℓ ⊥p

data ⊤p : Prop where
  tt : ⊤p

⊤p* : ∀ {ℓ} → Prop ℓ
⊤p* {ℓ} = LiftP ℓ ⊤p

pattern tt* = liftp tt 

absurdp : ∀ {ℓ ℓ'} {A : Set ℓ} → ⊥p* {ℓ'} → A
absurdp ()

⊥→⊥p : ⊥ → ⊥p
⊥→⊥p ()

infix 6 ¬_
¬_ : ∀ {ℓ} (X : Prop ℓ) → Prop ℓ
¬ X = X → ⊥p

_≢_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Prop ℓ
x ≢ y = ¬ (x ≡ y)

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
  infixr 3 _∨_
  data _∨_ : Prop (ℓ ⊔ ℓ') where
    inl : A → _∨_
    inr : B → _∨_

open ∨ public using (_∨_)

-- Bi-implication for propositions.
infix 3 _⇔_
_⇔_ : ∀ {ℓ ℓ'} (A : Prop ℓ) (B : Prop ℓ') → Prop (ℓ ⊔ ℓ')
A ⇔ B = (A → B) ∧ (B → A)

postulate
  propExt : ∀ {ℓA} → {A B : Prop ℓA}
          → A ⇔ B → A ≡ B

P∧Q→P≡Q : ∀ {ℓP} {P Q : Prop ℓP} → P ∧ Q → P ≡ Q
P∧Q→P≡Q (p , q) = propExt ((λ _ → q) , (λ _ → p))

