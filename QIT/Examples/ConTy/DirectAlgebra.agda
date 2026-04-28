module QIT.Examples.ConTy.DirectAlgebra where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base

record Algebra : Set₁ where
  field
    Con : Set
    Ty  : Con → Set
    ∙   : Con
    _▷_ : (Γ : Con) → Ty Γ → Con
    ι   : (Γ : Con) → Ty Γ
    π   : (Γ : Con) (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ

open Algebra public

record Hom (A B : Algebra) : Set₁ where
  private
    module A = Algebra A
    module B = Algebra B
  field
    conʰ : A.Con → B.Con
    tyʰ  : {Γ : A.Con} → A.Ty Γ → B.Ty (conʰ Γ)
    ∙ʰ   : conʰ A.∙ ≡ B.∙
    ▷ʰ   : ∀ {Γ} {T : A.Ty Γ} → conʰ (Γ A.▷ T) ≡ conʰ Γ B.▷ tyʰ T
    ιʰ   : ∀ {Γ} → tyʰ (A.ι Γ) ≡ B.ι (conʰ Γ)
    πʰ   : ∀ {Γ} {S : A.Ty Γ} {T : A.Ty (Γ A.▷ S)}
         → tyʰ (A.π Γ S T) ≡ B.π (conʰ Γ) (tyʰ S) (subst B.Ty ▷ʰ (tyʰ T))

open Algebra
open Hom

-- Derived: tyʰ commutes with subst
tyʰ-subst : {A B : Algebra} (f : Hom A B)
           → {Γ Γ' : Con A} (p : Γ ≡ Γ') (T : Ty A Γ)
           → tyʰ f (subst (Ty A) p T)
           ≡ subst (Ty B) (≡.cong (conʰ f) p) (tyʰ f T)
tyʰ-subst f ≡.refl T = ≡.refl

id : ∀ {A} → Hom A A
id = record
  { conʰ = λ Γ → Γ
  ; tyʰ  = λ T → T
  ; ∙ʰ   = ≡.refl
  ; ▷ʰ   = ≡.refl
  ; ιʰ   = ≡.refl
  ; πʰ   = ≡.refl
  }

_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
_∘_ {A} {B} {C} g f = record
  { conʰ = λ Γ → g.conʰ (f.conʰ Γ)
  ; tyʰ  = λ T → g.tyʰ (f.tyʰ T)
  ; ∙ʰ   = ≡.trans (≡.cong g.conʰ f.∙ʰ) g.∙ʰ
  ; ▷ʰ   = ≡.trans (≡.cong g.conʰ f.▷ʰ) g.▷ʰ
  ; ιʰ   = ≡.trans (≡.cong g.tyʰ f.ιʰ) g.ιʰ
  ; πʰ   = λ {Γ} {S} {T} → ≡.trans (≡.cong g.tyʰ f.πʰ) (w {Γ} {S} {T})
  }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  module f = Hom f
  module g = Hom g
  -- After applying f.πʰ and then g.πʰ, we need to rewrite the subst argument
  w : ∀ {Γ} {S : A.Ty Γ} {T : A.Ty (Γ A.▷ S)}
    → g.tyʰ (B.π (f.conʰ Γ) (f.tyʰ S) (subst B.Ty f.▷ʰ (f.tyʰ T)))
    ≡ C.π (g.conʰ (f.conʰ Γ)) (g.tyʰ (f.tyʰ S))
          (subst C.Ty (≡.trans (≡.cong g.conʰ f.▷ʰ) g.▷ʰ) (g.tyʰ (f.tyʰ T)))
  w {Γ} {S} {T} =
    g.tyʰ (B.π (f.conʰ Γ) (f.tyʰ S) (subst B.Ty f.▷ʰ (f.tyʰ T)))
      ≡⟨ g.πʰ ⟩
    C.π (g.conʰ (f.conʰ Γ)) (g.tyʰ (f.tyʰ S))
        (subst C.Ty g.▷ʰ (g.tyʰ (subst B.Ty f.▷ʰ (f.tyʰ T))))
      ≡⟨ ≡.cong (C.π (g.conʰ (f.conʰ Γ)) (g.tyʰ (f.tyʰ S))) q ⟩
    C.π (g.conʰ (f.conʰ Γ)) (g.tyʰ (f.tyʰ S))
        (subst C.Ty (≡.trans (≡.cong g.conʰ f.▷ʰ) g.▷ʰ) (g.tyʰ (f.tyʰ T))) ∎
    where
    open ≡.≡-Reasoning
    q : subst C.Ty g.▷ʰ (g.tyʰ (subst B.Ty f.▷ʰ (f.tyʰ T)))
      ≡ subst C.Ty (≡.trans (≡.cong g.conʰ f.▷ʰ) g.▷ʰ) (g.tyʰ (f.tyʰ T))
    q =
      subst C.Ty g.▷ʰ (g.tyʰ (subst B.Ty f.▷ʰ (f.tyʰ T)))
        ≡⟨ ≡.cong (subst C.Ty g.▷ʰ) (tyʰ-subst g f.▷ʰ (f.tyʰ T)) ⟩
      subst C.Ty g.▷ʰ (subst C.Ty (≡.cong g.conʰ f.▷ʰ) (g.tyʰ (f.tyʰ T)))
        ≡⟨ ≡.subst-subst {P = C.Ty} (≡.cong g.conʰ f.▷ʰ) {g.▷ʰ} ⟩
      subst C.Ty (≡.trans (≡.cong g.conʰ f.▷ʰ) g.▷ʰ) (g.tyʰ (f.tyʰ T)) ∎

-- Morphism equality: pointwise on Con, dependent on Ty
record _≈_ {A B : Algebra} (f g : Hom A B) : Prop ℓ0 where
  private
    module A = Algebra A
    module B = Algebra B
    module f = Hom f
    module g = Hom g
  field
    con≡ : ∀ Γ → f.conʰ Γ ≡ g.conʰ Γ
    ty≡  : ∀ {Γ} (T : A.Ty Γ)
          → subst B.Ty (con≡ Γ) (f.tyʰ T) ≡ g.tyʰ T

open _≈_

isEquiv≈ : ∀ {A B : Algebra} → IsEquivalence (_≈_ {A} {B})
isEquiv≈ {A} {B} = record
  { refl  = record
    { con≡ = λ _ → ≡.refl
    ; ty≡  = λ _ → ≡.refl
    }
  ; sym   = λ p → record
    { con≡ = λ Γ   → ≡.sym (con≡ p Γ)
    ; ty≡  = λ T   → ≡.dsym B.Ty (con≡ p _) (ty≡ p T)
    }
  ; trans = λ p q → record
    { con≡ = λ Γ   → ≡.trans (con≡ p Γ) (con≡ q Γ)
    ; ty≡  = λ T   → ≡.dtrans B.Ty (con≡ p _) (con≡ q _) (ty≡ p T) (ty≡ q T)
    }
  }
  where
  module A = Algebra A
  module B = Algebra B

∘-resp-≈ : ∀ {A B C : Algebra} {f h : Hom B C} {g i : Hom A B}
          → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {A} {B} {C} {f} {h} {g} {i} p q = record
  { con≡ = λ Γ →
      ≡.trans (≡.cong f.conʰ (con≡ q Γ)) (con≡ p (i.conʰ Γ))
  ; ty≡  = λ T →
      ≡.dtrans C.Ty
        (≡.cong f.conʰ (con≡ q _))
        (con≡ p (i.conʰ _))
        (≡.trans
          (≡.sym (tyʰ-subst f (con≡ q _) (g.tyʰ T)))
          (≡.cong f.tyʰ (ty≡ q T)))
        (ty≡ p (i.tyʰ T))
  }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  module f = Hom f
  module h = Hom h
  module g = Hom g
  module i = Hom i

Cat : Category (lsuc ℓ0) (lsuc ℓ0) ℓ0
Cat = record
  { Obj      = Algebra
  ; _⇒_      = Hom
  ; _≈_      = _≈_
  ; id       = id
  ; _∘_      = _∘_
  ; assoc    = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; sym-assoc = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; identityˡ = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; identityʳ = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; identity² = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; equiv     = isEquiv≈
  ; ∘-resp-≈  = ∘-resp-≈
  }
