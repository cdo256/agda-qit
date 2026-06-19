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

absurdp : ∀ {ℓ} {A : Set ℓ} → ⊥p → A
absurdp ()

absurdp' : ∀ {ℓ} {A : Prop ℓ} → ⊥p → A
absurdp' ()

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
_⇔_ : ∀ {ℓA ℓB} (A : Prop ℓA) (B : Prop ℓB) → Prop (ℓA ⊔ ℓB)
A ⇔ B = (A → B) ∧ (B → A)

⇔refl : ∀ {ℓA} {A : Prop ℓA} → A ⇔ A
⇔refl = (λ z → z) , (λ z → z)
⇔sym : ∀ {ℓA ℓB} {A : Prop ℓA} {B : Prop ℓB} → A ⇔ B → B ⇔ A
⇔sym (p₁ , p₂) = p₂ , p₁
⇔trans : ∀ {ℓA ℓB ℓC} {A : Prop ℓA} {B : Prop ℓB} {C : Prop ℓC}
     → A ⇔ B → B ⇔ C → A ⇔ C
⇔trans (p₁ , p₂) (q₁ , q₂) = (λ z → q₁ (p₁ z)) , (λ z → p₂ (q₂ z))

-- postulate
--   propExt : ∀ {ℓA} → {A B : Prop ℓA}
--           → A ⇔ B → A ≡ B

PropExt : Agda.Primitive.Propω
PropExt = ∀ {ℓA} 
  → {A B : Prop ℓA}
  → A ⇔ B → A ≡ B

-- P∧Q→P≡Q : ∀ {ℓP} {P Q : Prop ℓP} → P ∧ Q → P ≡ Q
-- P∧Q→P≡Q (p , q) = propExt ((λ _ → q) , (λ _ → p))

