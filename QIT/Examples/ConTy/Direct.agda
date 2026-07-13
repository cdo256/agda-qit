{-# OPTIONS --allow-unsolved-metas #-}
open import QIT.Prelude

module QIT.Examples.ConTy.Direct
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base
open import QIT.Relation.Subset

record Algebra ℓA : Set (lsuc ℓA) where
  infixl 5 _▷_
  field
    Con : Set ℓA
    Ty  : Con → Set ℓA
    ∙   : Con
    _▷_ : ∀ γ → Ty γ → Con
    u   : (γ : Con) → Ty γ
    π   : ∀ γ → (a : Ty γ) → (b : Ty (γ ▷ a)) → Ty γ
    σ   : ∀ γ → (a : Ty γ) → (b : Ty (γ ▷ a)) → Ty γ
    σ▷  : ∀ γ a b → γ ▷ a ▷ b ≡ γ ▷ σ γ a b
    σπ  : ∀ γ a b c → π γ a (π (γ ▷ a) b c) ≡ π γ (σ γ a b) (subst Ty (σ▷ γ a b) c)

open Algebra public

record Hom (A : Algebra ℓA) (B : Algebra ℓB) : Set (lsuc ℓA ⊔ lsuc ℓB) where
  private
    module A = Algebra A
    module B = Algebra B
  field
    conᴿ : A.Con → B.Con
    tyᴿ  : ∀ γ → A.Ty γ → B.Ty (conᴿ γ)
    ∙ᴿ   : conᴿ A.∙ ≡ B.∙
    ▷ᴿ   : ∀ γ a → conᴿ (γ A.▷ a) ≡ conᴿ γ B.▷ tyᴿ γ a
    uᴿ   : ∀ γ → tyᴿ γ (A.u γ) ≡ B.u (conᴿ γ)
    πᴿ   : ∀ γ a b → tyᴿ γ (A.π γ a b)
                      ≡ B.π (conᴿ γ) (tyᴿ γ a) (subst B.Ty (▷ᴿ γ a) (tyᴿ (γ A.▷ a) b))
    σᴿ   : ∀ γ a b → tyᴿ γ (A.σ γ a b)
                      ≡ B.σ (conᴿ γ) (tyᴿ γ a) (subst B.Ty (▷ᴿ γ a) (tyᴿ (γ A.▷ a) b))

open Hom public

-- Derived: tyᴿ commutes with subst
tyᴿ-subst : {A : Algebra ℓA} {B : Algebra ℓB} (f : Hom A B)
           → {γ γ' : Con A} (p : γ ≡ γ') (a : Ty A γ)
           → f .tyᴿ γ' (subst (Ty A) p a)
           ≡ subst (Ty B) (≡.cong (f .conᴿ) p) (f .tyᴿ γ a)
tyᴿ-subst f ≡.refl a = ≡.refl

id : ∀ {ℓA} {A} → Hom {ℓA} A A
id = record
  { conᴿ = λ γ → γ
  ; tyᴿ  = λ _ a → a
  ; ∙ᴿ   = ≡.refl
  ; ▷ᴿ   = λ _ _ → ≡.refl
  ; uᴿ   = λ _ → ≡.refl
  ; πᴿ   = λ _ _ _ → ≡.refl
  ; σᴿ   = λ _ _ _ → ≡.refl
  }

_∘_ : ∀ {A : Algebra ℓA} {B : Algebra ℓB} {C : Algebra ℓC}
    → Hom B C → Hom A B → Hom A C
_∘_ {A = A} {B} {C} g f = record
  { conᴿ = λ γ   → g.conᴿ (f.conᴿ γ)
  ; tyᴿ  = λ γ a → g.tyᴿ (f.conᴿ γ) (f.tyᴿ γ a)
  ; ∙ᴿ   = ≡.trans (≡.cong g.conᴿ f.∙ᴿ) g.∙ᴿ
  ; ▷ᴿ   = λ γ a → ≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a))
  ; uᴿ   = λ γ → ≡.trans (≡.cong (g.tyᴿ _) (f.uᴿ γ)) (g.uᴿ (f.conᴿ γ))
  ; πᴿ   = λ γ a b → ≡.trans (≡.cong (g.tyᴿ _) (f.πᴿ γ a b)) (w γ a b)
  ; σᴿ   = λ γ a b → ≡.trans (≡.cong (g.tyᴿ _) (f.σᴿ γ a b)) (v γ a b)
  }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  module f = Hom f
  module g = Hom g
  w : ∀ γ a b
    → g.tyᴿ _ (B.π (f.conᴿ γ) (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
    ≡ C.π (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))
          (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                      (g.tyᴿ _ (f.tyᴿ _ b)))
  w γ a b =
    g.tyᴿ _ (B.π (f.conᴿ γ) (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
      ≡⟨ g.πᴿ (f.conᴿ γ) (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)) ⟩
    C.π (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))
        (subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b))))
      ≡⟨ ≡.cong (C.π (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))) q ⟩
    C.π (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))
        (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                    (g.tyᴿ _ (f.tyᴿ _ b))) ∎
    where
    open ≡.≡-Reasoning
    q : subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
      ≡ subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                   (g.tyᴿ _ (f.tyᴿ _ b))
    q =
      subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
        ≡⟨ ≡.cong (subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a))) (tyᴿ-subst g (f.▷ᴿ γ a) (f.tyᴿ _ b)) ⟩
      subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a))
                 (subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.tyᴿ _ (f.tyᴿ _ b)))
        ≡⟨ ≡.subst-subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) _ ⟩
      subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                 (g.tyᴿ _ (f.tyᴿ _ b)) ∎
  v : ∀ γ a b
    → g.tyᴿ _ (B.σ (f.conᴿ γ) (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
    ≡ C.σ (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))
          (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                      (g.tyᴿ _ (f.tyᴿ _ b)))
  v γ a b =
    g.tyᴿ _ (B.σ (f.conᴿ γ) (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
      ≡⟨ g.σᴿ (f.conᴿ γ) (f.tyᴿ γ a) (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)) ⟩
    C.σ (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))
        (subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b))))
      ≡⟨ ≡.cong (C.σ (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))) q ⟩
    C.σ (g.conᴿ (f.conᴿ γ)) (g.tyᴿ _ (f.tyᴿ γ a))
        (subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                    (g.tyᴿ _ (f.tyᴿ _ b))) ∎
    where
    open ≡.≡-Reasoning
    q : subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
      ≡ subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                   (g.tyᴿ _ (f.tyᴿ _ b))
    q =
      subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) (g.tyᴿ _ (subst B.Ty (f.▷ᴿ γ a) (f.tyᴿ _ b)))
        ≡⟨ ≡.cong (subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a))) (tyᴿ-subst g (f.▷ᴿ γ a) (f.tyᴿ _ b)) ⟩
      subst C.Ty (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a))
                 (subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.tyᴿ _ (f.tyᴿ _ b)))
        ≡⟨ ≡.subst-subst C.Ty (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)) _ ⟩
      subst C.Ty (≡.trans (≡.cong g.conᴿ (f.▷ᴿ γ a)) (g.▷ᴿ (f.conᴿ γ) (f.tyᴿ γ a)))
                 (g.tyᴿ _ (f.tyᴿ _ b)) ∎

record _≈_ {A : Algebra ℓA} {B : Algebra ℓB} (f g : Hom A B) : Prop (ℓA ⊔ ℓB) where
  constructor mk≈
  field
    con≡ : ∀ γ   → f .conᴿ γ ≡ g .conᴿ γ
    ty≡  : ∀ γ a → subst (Ty B) (con≡ γ) (f .tyᴿ γ a) ≡ g .tyᴿ γ a

open _≈_ public

isEquiv≈ : ∀ {A : Algebra ℓA} {B : Algebra ℓB} → IsEquivalence (_≈_ {A = A} {B})
isEquiv≈ {A = A} {B} = record
  { refl  = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; sym   = λ (mk≈ c t) → mk≈ (λ γ   → ≡.sym (c γ))
                               (λ γ a → ≡.dsym (Ty B) (c γ) (t γ a))
  ; trans = λ (mk≈ cp tp) (mk≈ cq tq) →
      mk≈ (λ γ   → ≡.trans (cp γ) (cq γ))
          (λ γ a → ≡.dtrans (Ty B) (cp γ) (cq γ) (tp γ a) (tq γ a))
  }

∘-resp-≈ : ∀ {A B C : Algebra ℓA} {f h : Hom B C} {g i : Hom A B}
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

Cat : ∀ ℓA → Category (lsuc ℓA) (lsuc ℓA) ℓA
Cat ℓA = record
  { Obj       = Algebra ℓA
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

-- open import QIT.Category.Morphism Cat public
-- open import QIT.Category.Initial Cat public

LiftAlgebra : ∀ {ℓA} ℓB → Algebra ℓA → Algebra (ℓA ⊔ ℓB)
LiftAlgebra {ℓA} ℓB A = record
  { Con = Lift ℓB A.Con
  ; Ty = λ (lift γ) → Lift ℓB (A.Ty γ)
  ; ∙ = lift A.∙
  ; _▷_ = λ (lift γ) (lift a) → lift (γ A.▷ a)
  ; u = λ (lift γ) → lift (A.u γ)
  ; π = λ (lift γ) (lift a) (lift b) → lift (A.π γ a b)
  ; σ = λ (lift γ) (lift a) (lift b) → lift (A.σ γ a b)
  ; σ▷ = λ (lift γ) (lift a) (lift b) → ≡.cong lift (A.σ▷ γ a b)
  ; σπ = λ (lift γ) (lift a) (lift b) (lift c)
       → ≡.trans
           (≡.cong lift (A.σπ γ a b c))
           (≡.cong (π' (lift γ) (σ' (lift γ) (lift a) (lift b)))
                   (≡.sym (lift-subst (A.σ▷ γ a b) c)))
  }
  where
  module A = Algebra A 
  infixl 5 _▷'_
  Con' : Set (ℓA ⊔ ℓB)
  Con' = Lift ℓB A.Con
  Ty' : Con' → Set (ℓA ⊔ ℓB)
  Ty' (lift γ) = Lift ℓB (A.Ty γ)
  _▷'_ : ∀ γ → Ty' γ → Con'
  (lift γ) ▷' (lift a) = lift (γ A.▷ a)
  π' : ∀ γ → (a : Ty' γ) → (b : Ty' (γ ▷' a)) → Ty' γ
  π' (lift γ) (lift a) (lift b) = lift (A.π γ a b)
  σ' : ∀ γ → (a : Ty' γ) → (b : Ty' (γ ▷' a)) → Ty' γ
  σ' (lift γ) (lift a) (lift b) = lift (A.σ γ a b)

  lift-subst : ∀ {γ δ : A.Con} (p : γ ≡ δ) (a : A.Ty γ)
    → subst Ty' (≡.cong lift p) (lift a) ≡ lift (subst A.Ty p a)
  lift-subst ≡.refl a = ≡.refl

Lift⇒ : ∀ {ℓA} ℓB (A : Algebra ℓA) → Hom A (LiftAlgebra ℓB A)
Lift⇒ ℓB A = record
  { conᴿ = lift
  ; tyᴿ = λ _ a → lift a
  ; ∙ᴿ = ≡.refl
  ; ▷ᴿ = λ _ _ → ≡.refl
  ; uᴿ = λ _ → ≡.refl
  ; πᴿ = λ _ _ _ → ≡.refl
  ; σᴿ = λ _ _ _ → ≡.refl
  }

Lift⇐ : ∀ {ℓA} ℓB (A : Algebra ℓA) → Hom (LiftAlgebra ℓB A) A
Lift⇐ ℓB A = record
  { conᴿ = λ (lift γ) → γ
  ; tyᴿ = λ (lift γ) (lift a) → a
  ; ∙ᴿ = ≡.refl
  ; ▷ᴿ = λ (lift γ) (lift a) → ≡.refl
  ; uᴿ = λ (lift γ) → ≡.refl
  ; πᴿ = λ (lift γ) (lift a) (lift b) → ≡.refl
  ; σᴿ = λ (lift γ) (lift a) (lift b) → ≡.refl
  }

Lift⇒⇐ : ∀ {ℓA} ℓB (A : Algebra ℓA) → (Lift⇒ ℓB A ∘ Lift⇐ ℓB A) ≈ id
Lift⇒⇐ ℓB A = mk≈ (λ (lift γ) → ≡.refl) (λ (lift γ) (lift a) → ≡.refl)

Lift⇐⇒ : ∀ {ℓA} ℓB (A : Algebra ℓA) → (Lift⇐ ℓB A ∘ Lift⇒ ℓB A) ≈ id
Lift⇐⇒ ℓB A = mk≈ (λ γ → ≡.refl) (λ γ a → ≡.refl)
