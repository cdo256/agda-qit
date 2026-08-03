open import QIT.Prelude

module QIT.Examples.ConTy.MutualProjection
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base
open import QIT.Relation.Subset
open import QIT.Setoid

infixr 9 _∘_
infix  4 _≈_

record Algebra ℓA : Set (lsuc ℓA) where
  field
    Con : Set ℓA
    Ty : Set ℓA
    ty₁ : Ty → Con
    ∙ : Con
    ▷ : ∀ (γ : Con) (a : Ty)
      → (a₁ : ty₁ a ≡ γ)
      → Con
    u  : (γ : Con) → Ty
    u₁ : (γ : Con) → ty₁ (u γ) ≡ γ
    π : (γ : Con) (a b : Ty)
      → (a₁ : ty₁ a ≡ γ)
      → (b₁ : ty₁ b ≡ ▷ γ a a₁)
      → Ty
    π₁ : (γ : Con) (a b : Ty)
      → (a₁ : ty₁ a ≡ γ)
      → (b₁ : ty₁ b ≡ ▷ γ a a₁)
      → ty₁ (π γ a b a₁ b₁) ≡ γ
    σ : (γ : Con) (a b : Ty)
      → (a₁ : ty₁ a ≡ γ)
      → (b₁ : ty₁ b ≡ ▷ γ a a₁)
      → Ty
    σ₁ : (γ : Con) (a b : Ty)
      → (a₁ : ty₁ a ≡ γ)
      → (b₁ : ty₁ b ≡ ▷ γ a a₁)
      → ty₁ (σ γ a b a₁ b₁) ≡ γ
    σ▷ : (γ : Con) (a b : Ty)
      → (a₁ : ty₁ a ≡ γ)
      → (b₁ : ty₁ b ≡ ▷ γ a a₁)
      → ▷ (▷ γ a a₁) b b₁
      ≡ ▷ γ (σ γ a b a₁ b₁) (σ₁ γ a b a₁ b₁)
    σπ : (γ : Con) (a b c : Ty)
      → (a₁ : ty₁ a ≡ γ)
      → (b₁ : ty₁ b ≡ ▷ γ a a₁)
      → (c₁ : ty₁ c ≡ ▷ (▷ γ a a₁) b b₁)
      → π γ a (π (▷ γ a a₁) b c b₁ c₁)
            a₁ (π₁ (▷ γ a a₁) b c b₁ c₁)
      ≡ π γ (σ γ a b a₁ b₁) c
            (σ₁ γ a b a₁ b₁)
            (≡.trans c₁ (σ▷ γ a b a₁ b₁))

open Algebra public

record Hom (A : Algebra ℓA) (B : Algebra ℓB) : Set (lsuc ℓA ⊔ lsuc ℓB) where
  private
    module A = Algebra A
    module B = Algebra B
  field
    conᴿ : A.Con → B.Con
    tyᴿ  : A.Ty → B.Ty
    ty₁ᴿ : ∀ a → B.ty₁ (tyᴿ a) ≡ conᴿ (A.ty₁ a)
    ∙ᴿ   : conᴿ A.∙ ≡ B.∙
    ▷ᴿ   : ∀ γ a
      → (a₁ : A.ty₁ a ≡ γ)
      → (a₁' : B.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → conᴿ (A.▷ γ a a₁) ≡ B.▷ (conᴿ γ) (tyᴿ a) a₁'
    uᴿ   : ∀ γ → tyᴿ (A.u γ) ≡ B.u (conᴿ γ)
    πᴿ   : ∀ γ a b
      → (a₁ : A.ty₁ a ≡ γ)
      → (b₁ : A.ty₁ b ≡ A.▷ γ a a₁)
      → (a₁' : B.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → (b₁' : B.ty₁ (tyᴿ b) ≡ B.▷ (conᴿ γ) (tyᴿ a) a₁')
      → tyᴿ (A.π γ a b a₁ b₁)
      ≡ B.π (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
    σᴿ   : ∀ γ a b
      → (a₁ : A.ty₁ a ≡ γ)
      → (b₁ : A.ty₁ b ≡ A.▷ γ a a₁)
      → (a₁' : B.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → (b₁' : B.ty₁ (tyᴿ b) ≡ B.▷ (conᴿ γ) (tyᴿ a) a₁')
      → tyᴿ (A.σ γ a b a₁ b₁)
      ≡ B.σ (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'

open Hom public

id : ∀ {ℓA} {A} → Hom {ℓA} A A
id = record
  { conᴿ = λ γ → γ
  ; tyᴿ  = λ a → a
  ; ty₁ᴿ = λ _ → ≡.refl
  ; ∙ᴿ   = ≡.refl
  ; ▷ᴿ   = λ _ _ _ _ → ≡.refl
  ; uᴿ   = λ _ → ≡.refl
  ; πᴿ   = λ _ _ _ _ _ _ _ → ≡.refl
  ; σᴿ   = λ _ _ _ _ _ _ _ → ≡.refl
  }

_∘_ : ∀ {A : Algebra ℓA} {B : Algebra ℓB} {C : Algebra ℓC}
    → Hom B C → Hom A B → Hom A C
_∘_ {A = A} {B} {C} g f = record
  { conᴿ = λ γ → g.conᴿ (f.conᴿ γ)
  ; tyᴿ  = λ a → g.tyᴿ (f.tyᴿ a)
  ; ty₁ᴿ = λ a → ≡.trans (g.ty₁ᴿ (f.tyᴿ a)) (≡.cong g.conᴿ (f.ty₁ᴿ a))
  ; ∙ᴿ   = ≡.trans (≡.cong g.conᴿ f.∙ᴿ) g.∙ᴿ
  ; ▷ᴿ   = λ γ a a₁ a₁'' →
      ≡.trans
        (≡.cong g.conᴿ (f.▷ᴿ γ a a₁ (a₁' γ a a₁)))
        (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ a) (a₁' γ a a₁) a₁'')
  ; uᴿ   = λ γ → ≡.trans (≡.cong g.tyᴿ (f.uᴿ γ)) (g.uᴿ (f.conᴿ γ))
  ; πᴿ   = λ γ a b a₁ b₁ a₁'' b₁'' →
      ≡.trans
        (≡.cong g.tyᴿ (f.πᴿ γ a b a₁ b₁ (a₁' γ a a₁) (b₁' γ a b a₁ b₁)))
        (g.πᴿ (f.conᴿ γ) (f.tyᴿ a) (f.tyᴿ b)
          (a₁' γ a a₁) (b₁' γ a b a₁ b₁) a₁'' b₁'')
  ; σᴿ   = λ γ a b a₁ b₁ a₁'' b₁'' →
      ≡.trans
        (≡.cong g.tyᴿ (f.σᴿ γ a b a₁ b₁ (a₁' γ a a₁) (b₁' γ a b a₁ b₁)))
        (g.σᴿ (f.conᴿ γ) (f.tyᴿ a) (f.tyᴿ b)
          (a₁' γ a a₁) (b₁' γ a b a₁ b₁) a₁'' b₁'')
  }
  where
  module f = Hom f
  module g = Hom g

  a₁' : ∀ γ a → (a₁ : Algebra.ty₁ A a ≡ γ) → Algebra.ty₁ B (f.tyᴿ a) ≡ f.conᴿ γ
  a₁' γ a a₁ = ≡.trans (f.ty₁ᴿ a) (≡.cong f.conᴿ a₁)

  b₁' : ∀ γ a b
    → (a₁ : Algebra.ty₁ A a ≡ γ)
    → (b₁ : Algebra.ty₁ A b ≡ Algebra.▷ A γ a a₁)
    → Algebra.ty₁ B (f.tyᴿ b) ≡ Algebra.▷ B (f.conᴿ γ) (f.tyᴿ a) (a₁' γ a a₁)
  b₁' γ a b a₁ b₁ =
    ≡.trans
      (≡.trans (f.ty₁ᴿ b) (≡.cong f.conᴿ b₁))
      (f.▷ᴿ γ a a₁ (a₁' γ a a₁))

record _≈_ {A : Algebra ℓA} {B : Algebra ℓB} (f g : Hom A B) : Prop (ℓA ⊔ ℓB) where
  constructor mk≈
  module f = Hom f
  module g = Hom g
  field
    con≡ : ∀ γ → f.conᴿ γ ≡ g.conᴿ γ
    ty≡  : ∀ a → f.tyᴿ a ≡ g.tyᴿ a

open _≈_ public

isEquiv≈ : ∀ {A : Algebra ℓA} {B : Algebra ℓB} → IsEquivalence (_≈_ {A = A} {B})
isEquiv≈ = record
  { refl = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; sym = λ (mk≈ c t) → mk≈ (λ x → ≡.sym (c x)) (λ x → ≡.sym (t x))
  ; trans = λ (mk≈ c t) (mk≈ c' t') →
      mk≈ (λ x → ≡.trans (c x) (c' x)) (λ x → ≡.trans (t x) (t' x))
  }

HomSetoid : ∀ {ℓA ℓB} → (A : Algebra ℓA) (B : Algebra ℓB) → Setoid (lsuc ℓA ⊔ lsuc ℓB) (ℓA ⊔ ℓB)
HomSetoid A B = record
  { Carrier = Hom A B
  ; _≈_ = _≈_
  ; isEquivalence = isEquiv≈ }

∘-resp-≈ : ∀ {A : Algebra ℓA} {B : Algebra ℓB} {C : Algebra ℓC} {f h : Hom B C} {g i : Hom A B}
          → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} (mk≈ p pf) (mk≈ q qf) =
  mk≈
    (λ x → ≡.trans (≡.cong (f .conᴿ) (q x)) (p (i .conᴿ x)))
    (λ x → ≡.trans (≡.cong (f .tyᴿ) (qf x)) (pf (i .tyᴿ x)))

Cat : ∀ ℓA → Category (lsuc ℓA) (lsuc ℓA) ℓA
Cat ℓA = record
  { Obj       = Algebra ℓA
  ; _⇒_       = Hom
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; sym-assoc = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; identityˡ = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; identityʳ = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; identity² = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; equiv     = isEquiv≈
  ; ∘-resp-≈  = ∘-resp-≈
  }
