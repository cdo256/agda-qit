{-# OPTIONS --allow-unsolved-metas #-}
open import QIT.Prelude

module QIT.Examples.ConTy.Erased ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary

-- Following Setsini's 2023 thesis, sect 3.2.
data Con₀ : Set
data Ty₀ : Set

data Con₀ where
  ∙₀ : Con₀
  _▷₀_ : Con₀ → Ty₀ → Con₀

data Ty₀ where
  ι₀ : Con₀ → Ty₀
  π₀ : Con₀ → Ty₀ → Ty₀ → Ty₀

data Con₁ : Con₀ → Set
data Ty₁ : Con₀ → Ty₀ → Set

data Con₁ where
  ∙₁ : Con₁ ∙₀
  _▷₁_ : ∀ {Γ₀ A₀}
        → Con₁ Γ₀
        → Ty₁ Γ₀ A₀
        → Con₁ (Γ₀ ▷₀ A₀)

data Ty₁ where
  ι₁ : ∀ {Γ₀} (Γ₁ : Con₁ Γ₀) → Ty₁ Γ₀ (ι₀ Γ₀)
  π₁ : ∀ {Γ₀ A₀ B₀}
      → Con₁ Γ₀
      → Ty₁ Γ₀ A₀
      → Ty₁ (Γ₀ ▷₀ A₀) B₀
      → Ty₁ Γ₀ (π₀ Γ₀ A₀ B₀)

inv-ι₁ : ∀ {Γ₀ Δ₀} → Ty₁ Γ₀ (ι₀ Δ₀) → Γ₀ ≡ Δ₀
inv-ι₁ {∙₀} {∙₀} A₁ = ≡.refl
inv-ι₁ {Γ₀ ▷₀ _} {Γ₀ ▷₀ _} (ι₁ Γ₁) = ≡.refl

inv-π₁ : ∀ {Γ₀ Δ₀ A₀ B₀} → Ty₁ Γ₀ (π₀ Δ₀ A₀ B₀) → Γ₀ ≡ Δ₀
inv-π₁ (π₁ Δ₁ A₁ B₁) = ≡.refl

isPropCon₁ : ∀ {Γ₀} → isProp (Con₁ Γ₀)
isPropTy₁ : ∀ {Γ₀ A₀} → isProp (Ty₁ Γ₀ A₀)

isPropCon₁ ∙₁ ∙₁ =
  ≡.refl
isPropCon₁ (Γ₁ ▷₁ A₁) (Δ₁ ▷₁ B₁) =
  ≡.cong₂ _▷₁_ (isPropCon₁ Γ₁ Δ₁) (isPropTy₁ A₁ B₁)

isPropTy₁ (ι₁ Γ₁) (ι₁ Δ₁) =
  ≡.cong ι₁ (isPropCon₁ Γ₁ Δ₁)
isPropTy₁ (π₁ Γ₁ A₁ B₁) (π₁ Δ₁ C₁ D₁) =
  ≡.cong₃ π₁ (isPropCon₁ Γ₁ Δ₁) (isPropTy₁ A₁ C₁) (isPropTy₁ B₁ D₁)

Con : Set
Con = Σ Con₀ Con₁

Ty : Con → Set
Ty (Γ₀ , _) = Σ Ty₀ (Ty₁ Γ₀)

∙ : Con
∙ = ∙₀ , ∙₁
_▷_ : (Γ : Con) → Ty Γ → Con
(Γ₀ , Γ₁) ▷ (A₀ , A₁) = (Γ₀ ▷₀ A₀) , (Γ₁ ▷₁ A₁)

ι : (Γ : Con) → Ty Γ
ι (Γ₀ , Γ₁) = ι₀ Γ₀ , ι₁ Γ₁
π : (Γ : Con) → (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
π (Γ₀ , Γ₁) (A₀ , A₁) (B₀ , B₁) = π₀ Γ₀ A₀ B₀ , π₁ Γ₁ A₁ B₁

-- Motive/methods
record Algebra : Set₁ where
  field
    Conᴬ : Set
    Tyᴬ : Conᴬ → Set
    ∙ᴬ : Conᴬ
    _▷ᴬ_ : (Γᴬ : Conᴬ) → (A : Tyᴬ Γᴬ) → Conᴬ
    ιᴬ : (Γᴬ : Conᴬ) → Tyᴬ Γᴬ
    πᴬ : (Γᴬ : Conᴬ) (Aᴬ : Tyᴬ Γᴬ) (Bᴬ : Tyᴬ (Γᴬ ▷ᴬ Aᴬ))
        → Tyᴬ Γᴬ

record DisplayedAlgebra : Set₁ where
  field
    Conᴰ : Con → Set
    Tyᴰ : {Γ : Con} → Conᴰ Γ → Ty Γ → Set
    ∙ᴰ : Conᴰ ∙
    _▷ᴰ_ : ∀ {Γ A} (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ A → Conᴰ (Γ ▷ A)
    ιᴰ : ∀ {Γ} (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ (ι Γ)
    πᴰ : ∀ {Γ A B} (Γᴰ : Conᴰ Γ) (Aᴰ : Tyᴰ Γᴰ A) (Bᴰ : Tyᴰ (Γᴰ ▷ᴰ Aᴰ) B)
        → Tyᴰ Γᴰ (π Γ A B)

record Rec (A : Algebra) : Set₁ where
    open Algebra A
    field
      conᴿ : Con → Conᴬ
      tyᴿ : {Γ : Con} → Ty Γ → Tyᴬ (conᴿ Γ)
      ∙ᴿ : conᴿ ∙ ≡ ∙ᴬ
      ▷ᴿ : ∀ {Γ A} → conᴿ (Γ ▷ A) ≡ (conᴿ Γ) ▷ᴬ (tyᴿ A)
      ιᴿ : ∀ {Γ} → tyᴿ (ι Γ) ≡ ιᴬ (conᴿ Γ)
      πᴿ : ∀ {Γ A B} → tyᴿ (π Γ A B)
                      ≡ πᴬ (conᴿ Γ) (tyᴿ A) (subst Tyᴬ ▷ᴿ (tyᴿ B))

record Rec≡ (A : Algebra) (r s : Rec A) : Set where
  private
    open Algebra A
    module r = Rec r
    module s = Rec s
  field
    con≡ : ∀ Γ → r.conᴿ Γ ≡ s.conᴿ Γ
    ty≡ : ∀ Γ → (A : Ty Γ) → subst Tyᴬ (con≡ Γ) (r.tyᴿ A) ≡ s.tyᴿ A

reflRec≡ : {A : Algebra} {r : Rec A} → Rec≡ A r r
reflRec≡ = record
  { con≡ = λ _ → ≡.refl
  ; ty≡ = λ _ _ → ≡.refl
  }

symRec≡ : {A : Algebra} {r s : Rec A} → Rec≡ A r s → Rec≡ A s r
symRec≡ {A} p = record
  { con≡ = λ Γ → ≡.sym (con≡ p Γ)
  ; ty≡ = λ Γ B → ≡.dsym Tyᴬ (con≡ p Γ) (ty≡ p Γ B)
  }
  where
  open Algebra A
  open Rec≡

transRec≡ : {A : Algebra} {r s t : Rec A} → Rec≡ A r s → Rec≡ A s t → Rec≡ A r t
transRec≡ {A} p q = record
  { con≡ = λ Γ → ≡.trans (con≡ p Γ) (con≡ q Γ)
  ; ty≡ = λ Γ B → ≡.dtrans Tyᴬ (con≡ p Γ) (con≡ q Γ) (ty≡ p Γ B) (ty≡ q Γ B)
  }
  where
  open Algebra A
  open Rec≡

record Elim (D : DisplayedAlgebra) : Set₁ where
    open DisplayedAlgebra D
    field
      conᴱ : (Γ : Con) → Conᴰ Γ
      tyᴱ : {Γ : Con} (A : Ty Γ) → Tyᴰ (conᴱ Γ) A
      ∙ᴱ : conᴱ ∙ ≡ ∙ᴰ
      ▷ᴱ : ∀ {Γ A} → conᴱ (Γ ▷ A) ≡ conᴱ Γ ▷ᴰ tyᴱ A
      ιᴱ : ∀ {Γ} → tyᴱ (ι Γ) ≡ ιᴰ (conᴱ Γ)
      πᴱ : ∀ {Γ A B}
          → tyᴱ (π Γ A B)
          ≡ πᴰ (conᴱ Γ) (tyᴱ A) (subst (λ Δ → Tyᴰ Δ B) ▷ᴱ (tyᴱ B))

record Elim≡ (D : DisplayedAlgebra) (r s : Elim D) : Set where
  private
    open DisplayedAlgebra D
    module r = Elim r
    module s = Elim s
  field
    con≡ : ∀ Γ → r.conᴱ Γ ≡ s.conᴱ Γ
    ty≡ : ∀ Γ → (A : Ty Γ) → ≡.subst (λ ○ → Tyᴰ ○ A) (con≡ Γ) (r.tyᴱ A) ≡ s.tyᴱ A

reflElim≡ : {D : DisplayedAlgebra} {r : Elim D} → Elim≡ D r r
reflElim≡ = record
  { con≡ = λ _ → ≡.refl
  ; ty≡ = λ _ _ → ≡.refl
  }

symElim≡ : {D : DisplayedAlgebra} {r s : Elim D} → Elim≡ D r s → Elim≡ D s r
symElim≡ {D} p = record
  { con≡ = λ Γ → ≡.sym (con≡ p Γ)
  ; ty≡ = λ Γ A → ≡.dsym (λ ○ → Tyᴰ ○ A) (con≡ p Γ) (ty≡ p Γ A)
  }
  where
  open DisplayedAlgebra D
  open Elim≡

transElim≡ : {D : DisplayedAlgebra} {r s t : Elim D} → Elim≡ D r s → Elim≡ D s t → Elim≡ D r t
transElim≡ {D} p q = record
  { con≡ = λ Γ → ≡.trans (con≡ p Γ) (con≡ q Γ)
  ; ty≡ = λ Γ A → ≡.dtrans (λ ○ → Tyᴰ ○ A) (con≡ p Γ) (con≡ q Γ) (ty≡ p Γ A) (ty≡ q Γ A)
  }
  where
  open DisplayedAlgebra D
  open Elim≡


∃!Elim : DisplayedAlgebra → Set₁
∃!Elim D = Σ (Elim D) λ r → ∀ r' → Elim≡ D r r'

∃!Rec : Algebra → Set₁
∃!Rec A = Σ (Rec A) λ r → ∀ r' → Rec≡ A r r'

TotalAlgebra : DisplayedAlgebra → Algebra
TotalAlgebra D = record
  { Conᴬ = Σ Con Conᴰ
  ; Tyᴬ = λ (Γ , Γᴰ) → Σ (Ty Γ) (Tyᴰ Γᴰ)
  ; ∙ᴬ = ∙ , ∙ᴰ
  ; _▷ᴬ_ = λ (Γ , Γᴰ) (A , Aᴰ) → (Γ ▷ A) , (Γᴰ ▷ᴰ Aᴰ)
  ; ιᴬ = λ (Γ , Γᴰ) → ι Γ , ιᴰ Γᴰ
  ; πᴬ = λ (Γ , Γᴰ) (A , Aᴰ) (B , Bᴰ) → π Γ A B , πᴰ Γᴰ Aᴰ Bᴰ
  }
  where open DisplayedAlgebra D

BaseAlgebra : Algebra
BaseAlgebra = record
  { Conᴬ = Con
  ; Tyᴬ = Ty
  ; ∙ᴬ = ∙
  ; _▷ᴬ_ = _▷_
  ; ιᴬ = ι
  ; πᴬ = π }

idRec : Rec BaseAlgebra
idRec = record
  { conᴿ = λ Γ → Γ
  ; tyᴿ = λ A → A
  ; ∙ᴿ = ≡.refl
  ; ▷ᴿ = ≡.refl
  ; ιᴿ = ≡.refl
  ; πᴿ = ≡.refl }

record AlgebraHom (A B : Algebra) : Set₁ where
  module A = Algebra A
  module B = Algebra B
  field
    conʰ : A.Conᴬ → B.Conᴬ
    tyʰ : {Γᴬ : A.Conᴬ} → A.Tyᴬ Γᴬ → B.Tyᴬ (conʰ Γᴬ)
    ∙ʰ : conʰ A.∙ᴬ ≡ B.∙ᴬ
    ▷ʰ : ∀ {Γᴬ Aᴬ} → conʰ (Γᴬ A.▷ᴬ Aᴬ) ≡ conʰ Γᴬ B.▷ᴬ tyʰ Aᴬ
    ιʰ : ∀ {Γᴬ} → tyʰ (A.ιᴬ Γᴬ) ≡ B.ιᴬ (conʰ Γᴬ)
    πʰ : ∀ {Γᴬ Aᴬ Bᴬ} → tyʰ (A.πᴬ Γᴬ Aᴬ Bᴬ)
                      ≡ B.πᴬ (conʰ Γᴬ) (tyʰ Aᴬ) (subst B.Tyᴬ ▷ʰ (tyʰ Bᴬ))

tyʰ-subst : {A B : Algebra} (f : AlgebraHom A B)
          → {Γᴬ Γᴬ' : Algebra.Conᴬ A} (p : Γᴬ ≡ Γᴬ') (Aᴬ : Algebra.Tyᴬ A Γᴬ)
          → AlgebraHom.tyʰ f (subst (Algebra.Tyᴬ A) p Aᴬ)
          ≡ subst (Algebra.Tyᴬ B) (≡.cong (AlgebraHom.conʰ f) p) (AlgebraHom.tyʰ f Aᴬ)
tyʰ-subst f ≡.refl Aᴬ = ≡.refl

AlgebraComp : {A B : Algebra} → Rec A → AlgebraHom A B → Rec B
AlgebraComp {A} {B} r f = record
  { conᴿ = λ Γ → f.conʰ (r.conᴿ Γ)
  ; tyᴿ = λ A → f.tyʰ (r.tyᴿ A)
  ; ∙ᴿ = ≡.trans (≡.cong f.conʰ r.∙ᴿ) f.∙ʰ
  ; ▷ᴿ = ≡.trans (≡.cong f.conʰ r.▷ᴿ) f.▷ʰ
  ; ιᴿ = ≡.trans (≡.cong f.tyʰ r.ιᴿ) f.ιʰ
  ; πᴿ = λ {Γ A B} → ≡.trans (≡.cong f.tyʰ r.πᴿ) w }
  where
  module A = Algebra A
  module B = Algebra B
  module r = Rec r
  module f = AlgebraHom f
  w : ∀ {Γ A B}
    → f.tyʰ (f.A.πᴬ (r.conᴿ Γ) (r.tyᴿ A)
            (subst f.A.Tyᴬ r.▷ᴿ (r.tyᴿ B)))
    ≡ f.B.πᴬ (f.conʰ (r.conᴿ Γ)) (f.tyʰ (r.tyᴿ A))
              (subst f.B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ᴿ) f.▷ʰ) (f.tyʰ (r.tyᴿ B)))
  w {Γ} {A} {B} =
    f.tyʰ (A.πᴬ (r.conᴿ Γ) (r.tyᴿ A) (subst A.Tyᴬ r.▷ᴿ (r.tyᴿ B)))
      ≡⟨ f.πʰ ⟩
    B.πᴬ (f.conʰ (r.conᴿ Γ)) (f.tyʰ (r.tyᴿ A))
          (subst B.Tyᴬ f.▷ʰ (f.tyʰ (subst A.Tyᴬ r.▷ᴿ (r.tyᴿ B))))
      ≡⟨ ≡.cong (B.πᴬ (f.conʰ (r.conᴿ Γ)) (f.tyʰ (r.tyᴿ A))) q ⟩
    B.πᴬ (f.conʰ (r.conᴿ Γ)) (f.tyʰ (r.tyᴿ A))
          (subst B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ᴿ) f.▷ʰ) (f.tyʰ (r.tyᴿ B))) ∎
    where
    open ≡.≡-Reasoning
    q : subst B.Tyᴬ f.▷ʰ (f.tyʰ (subst A.Tyᴬ r.▷ᴿ (r.tyᴿ B)))
      ≡ subst B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ᴿ) f.▷ʰ) (f.tyʰ (r.tyᴿ B))
    q =
      subst B.Tyᴬ f.▷ʰ (f.tyʰ (subst A.Tyᴬ r.▷ᴿ (r.tyᴿ B)))
        ≡⟨ ≡.cong (subst B.Tyᴬ f.▷ʰ) (tyʰ-subst f r.▷ᴿ (r.tyᴿ B)) ⟩
      subst B.Tyᴬ f.▷ʰ (subst B.Tyᴬ (≡.cong f.conʰ r.▷ᴿ) (f.tyʰ (r.tyᴿ B)))
        ≡⟨ ≡.subst-subst B.Tyᴬ (≡.cong f.conʰ r.▷ᴿ) f.▷ʰ (f.tyʰ (r.tyᴿ B)) ⟩
      subst B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ᴿ) f.▷ʰ) (f.tyʰ (r.tyᴿ B)) ∎
