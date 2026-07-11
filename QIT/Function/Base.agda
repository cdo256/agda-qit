open import QIT.Prelude

module QIT.Function.Base ⦃ pathElim* : PathElim ⦄ where

open import QIT.Prop

Surjective : ∀ {A : Set ℓA} {B : Set ℓB}
           → (A → B) → Prop _
Surjective f = ∀ y → ∃ λ x → f x ≡ y

Surjection : (A : Set ℓA) (B : Set ℓB) → Set _
Surjection A B = ΣP (A → B) Surjective

_↠_ = Surjection

-- Bijections between sets - one-to-one correspondences with explicit inverses.
module ≅ˢ where
  record _≅ˢ_ (X : Set ℓX) (Y : Set ℓY) : Set (ℓX ⊔ ℓY) where
    field
      to : X → Y
      from : Y → X
      rinv : ∀ x → from (to x) ≡ x
      linv : ∀ y → to (from y) ≡ y

  open _≅ˢ_ public

  refl : {X : Set ℓX} → X ≅ˢ X
  refl = record
    { to = λ x → x
    ; from = λ x → x
    ; rinv = λ _ → ≡.refl
    ; linv = λ _ → ≡.refl }

  sym : {X : Set ℓX} {Y : Set ℓY} → X ≅ˢ Y → Y ≅ˢ X
  sym X≅Y = record
    { to = X≅Y .from
    ; from = X≅Y .to
    ; rinv = X≅Y .linv
    ; linv = X≅Y .rinv }
    where open _≅ˢ_ X≅Y

  _∘_ : {X : Set ℓX} {Y : Set ℓY} {Z : Set ℓZ} → Y ≅ˢ Z → X ≅ˢ Y → X ≅ˢ Z
  q ∘ p = record
    { to = λ x → q.to (p.to x)
    ; from = λ z → p.from (q.from z)
    ; rinv = λ x → ≡.trans (≡.cong p.from (q.rinv (p.to x))) (p.rinv x)
    ; linv = λ z → ≡.trans (≡.cong q.to (p.linv (q.from z))) (q.linv z) }
    where
    module p = _≅ˢ_ p
    module q = _≅ˢ_ q

open ≅ˢ using (_≅ˢ_) public

matchp : {A : Prop ℓA} {B : A → Prop ℓB} → (a : A) → (f : ∀ a → B a) → B a
matchp x f = f x

infixr 5 _∘_
_∘_ : ∀ {A : Set ℓA} {B : A → Set ℓB} {C : A → Set ℓC}
    → (g : ∀ {a} → (b : B a) → C a)
    → (f : (a : A) → B a)
    → ∀ a → C a
(g ∘ f) a = g (f a)

infixr 5 _∘ᵖ_
_∘ᵖ_ : ∀ {A : Prop ℓA} {B : A → Prop ℓB} {C : A → Set ℓC}
    → (g : ∀ {a} → (b : B a) → C a)
    → (f : (a : A) → B a)
    → ∀ a → C a
(g ∘ᵖ f) a = g (f a)

infixr 5 _∘ˢᵖ_
_∘ˢᵖ_ : ∀ {A : Set ℓA} {B : A → Prop ℓB} {C : A → Set ℓC}
    → (g : ∀ {a} → (b : B a) → C a)
    → (f : (a : A) → B a)
    → ∀ a → C a
(g ∘ˢᵖ f) a = g (f a)

infixr 5 _∘ᵖˢ_
_∘ᵖˢ_ : ∀ {A : Prop ℓA} {B : A → Set ℓB} {C : A → Set ℓC}
    → (g : ∀ {a} → (b : B a) → C a)
    → (f : (a : A) → B a)
    → ∀ a → C a
(g ∘ᵖˢ f) a = g (f a)

const : ∀ {A : Set ℓA} {B : Set ℓB} → A → B → A
const a _ = a

Π : (A : Set ℓA) (B : A → Set ℓB) → Set (ℓA ⊔ ℓB)
Π A B = (a : A) → B a
