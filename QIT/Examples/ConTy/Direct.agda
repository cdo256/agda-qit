module QIT.Examples.ConTy.Direct where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base
open import QIT.Relation.Subset

record Algebra : Set₁ where
  infixl 5 _▷_
  field
    Con : Set
    Ty  : Con → Set
    ∙   : Con
    _▷_ : ∀ γ → Ty γ → Con
    u   : (γ : Con) → Ty γ
    π   : ∀ {γ} → (a : Ty γ) → (b : Ty (γ ▷ a)) → Ty γ
    σ   : ∀ {γ} → (a : Ty γ) → (b : Ty (γ ▷ a)) → Ty γ
    σ▷  : ∀ {γ a b} → γ ▷ a ▷ b ≡ γ ▷ σ a b
    σπ  : ∀ {γ a b c} → π {γ} a (π b c) ≡ π (σ a b) (subst Ty σ▷ c)

open Algebra public

record Hom (A B : Algebra) : Set₁ where
  private
    module A = Algebra A
    module B = Algebra B
  field
    conᴿ : A.Con → B.Con
    tyᴿ  : ∀ γ → A.Ty γ → B.Ty (conᴿ γ)
    ∙ᴿ   : conᴿ A.∙ ≡ B.∙
    ▷ᴿ   : ∀ {γ} a → conᴿ (γ A.▷ a) ≡ conᴿ γ B.▷ tyᴿ γ a
    uᴿ   : ∀ {γ} → tyᴿ γ (A.u γ) ≡ B.u (conᴿ γ)
    πᴿ   : ∀ {γ} a b → tyᴿ γ (A.π a b)
                      ≡ B.π (tyᴿ γ a) (subst B.Ty (▷ᴿ a) (tyᴿ (γ A.▷ a) b))
    σᴿ   : ∀ {γ} a b → tyᴿ γ (A.σ a b)
                      ≡ B.σ (tyᴿ γ a) (subst B.Ty (▷ᴿ a) (tyᴿ (γ A.▷ a) b))

open Hom public

-- Derived: tyᴿ commutes with subst
tyᴿ-subst : {A B : Algebra} (f : Hom A B)
           → {γ γ' : Con A} (p : γ ≡ γ') (a : Ty A γ)
           → f .tyᴿ γ' (subst (Ty A) p a)
           ≡ subst (Ty B) (≡.cong (f .conᴿ) p) (f .tyᴿ γ a)
tyᴿ-subst f ≡.refl a = ≡.refl

id : ∀ {A} → Hom A A
id = record
  { conᴿ = λ γ → γ
  ; tyᴿ  = λ _ a → a
  ; ∙ᴿ   = ≡.refl
  ; ▷ᴿ   = λ _ → ≡.refl
  ; uᴿ   = ≡.refl
  ; πᴿ   = λ _ _ → ≡.refl
  ; σᴿ   = λ _ _ → ≡.refl
  }

_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
_∘_ {A} {B} {C} g f = record
  { conᴿ = λ γ   → g.conᴿ (f.conᴿ γ)
  ; tyᴿ  = λ γ a → g.tyᴿ (f.conᴿ γ) (f.tyᴿ γ a)
  ; ∙ᴿ   = ≡.trans (≡.cong g.conᴿ f.∙ᴿ) g.∙ᴿ
  ; ▷ᴿ   = λ a   → ≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a))
  ; uᴿ   = ≡.trans (≡.cong (g.tyᴿ _) f.uᴿ) g.uᴿ
  ; πᴿ   = λ {γ} a b → ≡.trans (≡.cong (g.tyᴿ _) (f.πᴿ a b)) (w a b)
  ; σᴿ   = λ {γ} a b → ≡.trans (≡.cong (g.tyᴿ _) (f.σᴿ a b)) (v a b)
  }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  module f = Hom f
  module g = Hom g
  w : ∀ {γ} a b
    → g.tyᴿ _ (B.π (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
    ≡ C.π (g.tyᴿ _ (f.tyᴿ γ a))
          (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                      (g.tyᴿ _ (f.tyᴿ _ b)))
  w a b =
    g.tyᴿ _ (B.π (f.tyᴿ _ a) (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
      ≡⟨ g.πᴿ (f.tyᴿ _ a) (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)) ⟩
    C.π (g.tyᴿ _ (f.tyᴿ _ a))
        (subst C.Ty (g.▷ᴿ (f.tyᴿ _ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b))))
      ≡⟨ ≡.cong (C.π _) q ⟩
    C.π (g.tyᴿ _ (f.tyᴿ _ a))
        (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                    (g.tyᴿ _ (f.tyᴿ _ b))) ∎
    where
    open ≡.≡-Reasoning
    q : subst C.Ty (g.▷ᴿ (f.tyᴿ _ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
      ≡ subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                   (g.tyᴿ _ (f.tyᴿ _ b))
    q =
      subst C.Ty (g.▷ᴿ (f.tyᴿ _ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
        ≡⟨ ≡.cong (subst C.Ty (g.▷ᴿ _)) (tyᴿ-subst g (f.▷ᴿ a) (f.tyᴿ _ b)) ⟩
      subst C.Ty (g.▷ᴿ (f.tyᴿ _ a))
                 (subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ a)) (g.tyᴿ _ (f.tyᴿ _ b)))
        ≡⟨ ≡.subst-subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)) _ ⟩
      subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                 (g.tyᴿ _ (f.tyᴿ _ b)) ∎
  v : ∀ {γ} a b
    → g.tyᴿ _ (B.σ (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
    ≡ C.σ (g.tyᴿ _ (f.tyᴿ γ a))
          (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                      (g.tyᴿ _ (f.tyᴿ _ b)))
  v a b =
    g.tyᴿ _ (B.σ (f.tyᴿ _ a) (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
      ≡⟨ g.σᴿ (f.tyᴿ _ a) (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)) ⟩
    C.σ (g.tyᴿ _ (f.tyᴿ _ a))
        (subst C.Ty (g.▷ᴿ (f.tyᴿ _ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b))))
      ≡⟨ ≡.cong (C.σ _) q ⟩
    C.σ (g.tyᴿ _ (f.tyᴿ _ a))
        (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                    (g.tyᴿ _ (f.tyᴿ _ b))) ∎
    where
    open ≡.≡-Reasoning
    q : subst C.Ty (g.▷ᴿ (f.tyᴿ _ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
      ≡ subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                   (g.tyᴿ _ (f.tyᴿ _ b))
    q =
      subst C.Ty (g.▷ᴿ (f.tyᴿ _ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ a) (f.tyᴿ _ b)))
        ≡⟨ ≡.cong (subst C.Ty (g.▷ᴿ _)) (tyᴿ-subst g (f.▷ᴿ a) (f.tyᴿ _ b)) ⟩
      subst C.Ty (g.▷ᴿ (f.tyᴿ _ a))
                 (subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ a)) (g.tyᴿ _ (f.tyᴿ _ b)))
        ≡⟨ ≡.subst-subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)) _ ⟩
      subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ a)) (g.▷ᴿ (f.tyᴿ _ a)))
                 (g.tyᴿ _ (f.tyᴿ _ b)) ∎

record _≈_ {A B : Algebra} (f g : Hom A B) : Prop ℓ0 where
  constructor mk≈
  field
    con≡ : ∀ γ   → f .conᴿ γ ≡ g .conᴿ γ
    ty≡  : ∀ γ a → subst (Ty B) (con≡ γ) (f .tyᴿ γ a) ≡ g .tyᴿ γ a

open _≈_ public

isEquiv≈ : ∀ {A B : Algebra} → IsEquivalence (_≈_ {A} {B})
isEquiv≈ {A} {B} = record
  { refl  = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; sym   = λ (mk≈ c t) → mk≈ (λ γ   → ≡.sym (c γ))
                               (λ γ a → ≡.dsym (Ty B) (c γ) (t γ a))
  ; trans = λ (mk≈ cp tp) (mk≈ cq tq) →
      mk≈ (λ γ   → ≡.trans (cp γ) (cq γ))
          (λ γ a → ≡.dtrans (Ty B) (cp γ) (cq γ) (tp γ a) (tq γ a))
  }

∘-resp-≈ : ∀ {A B C : Algebra} {f h : Hom B C} {g i : Hom A B}
          → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {C = C} {f = f} {h} {g} {i} (mk≈ cp tp) (mk≈ cq tq) = mk≈
  (λ γ   → ≡.trans (≡.cong (f .conᴿ) (cq γ)) (cp (i .conᴿ γ)))
  (λ γ a →
    ≡.dtrans (Ty C)
      (≡.cong (f .conᴿ) (cq γ))
      (cp (i .conᴿ γ))
      (≡.trans (≡.sym (tyᴿ-subst f (cq γ) (g .tyᴿ γ a)))
               (≡.cong (f .tyᴿ _) (tq γ a)))
      (tp (i .conᴿ γ) (i .tyᴿ γ a)))

Cat : Category (lsuc ℓ0) (lsuc ℓ0) ℓ0
Cat = record
  { Obj       = Algebra
  ; _⇒_       = Hom
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; sym-assoc = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; identityˡ = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; identityʳ = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; identity² = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; equiv     = isEquiv≈
  ; ∘-resp-≈  = ∘-resp-≈
  }

open import QIT.Category.Morphism Cat public
open import QIT.Category.Initial Cat public
