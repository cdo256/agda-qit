{-# OPTIONS --allow-unsolved-metas #-}
module QIT.Examples.ConTy.Algebra where

open import QIT.Prelude
open import QIT.Prop
-- open import QIT.Prop.HetPath as ≣ using (_≣_)
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary

open ≡

record Algebra : Set₁ where
  field
    Conᴬ : Set
    Tyᴬ : Conᴬ → Set
    ∙ᴬ : Conᴬ
    _▷ᴬ_ : (Γᴬ : Conᴬ) → (A : Tyᴬ Γᴬ) → Conᴬ
    ιᴬ : (Γᴬ : Conᴬ) → Tyᴬ Γᴬ
    πᴬ : (Γᴬ : Conᴬ) (Aᴬ : Tyᴬ Γᴬ) (Bᴬ : Tyᴬ (Γᴬ ▷ᴬ Aᴬ))
        → Tyᴬ Γᴬ

record Hom (A B : Algebra) : Set₁ where
    module A = Algebra A
    module B = Algebra B
    field
      conʳ : A.Conᴬ → B.Conᴬ
      tyʳ : {Γ : A.Conᴬ} → A.Tyᴬ Γ → B.Tyᴬ (conʳ Γ)
      ∙ʳ : conʳ A.∙ᴬ ≡ B.∙ᴬ 
      ▷ʳ : ∀ {Γ A} → conʳ (Γ A.▷ᴬ A) ≡ (conʳ Γ B.▷ᴬ (tyʳ A))
      ιʳ : ∀ {Γ} → tyʳ (A.ιᴬ Γ) ≡ B.ιᴬ (conʳ Γ)
      πʳ : ∀ {Γ A B}
        → tyʳ (A.πᴬ Γ A B)
        ≡ B.πᴬ (conʳ Γ) (tyʳ A) (≡.subst B.Tyᴬ ▷ʳ (tyʳ B))

record _≡ʳ_ {A B : Algebra} (r s : Hom A B) : Set where
  module A = Algebra A
  module B = Algebra B
  module r = Hom r
  module s = Hom s
  field
    con≡ : ∀ Γ → r.conʳ Γ ≡ s.conʳ Γ
    ty≡ : ∀ Γ → (A : A.Tyᴬ Γ)
        → subst B.Tyᴬ (con≡ Γ) (r.tyʳ {Γ} A)
        ≡ s.tyʳ {Γ} A

module _ {A B : Algebra} where
  open _≡ʳ_
  refl≡ʳ : {r : Hom A B} → r ≡ʳ r
  refl≡ʳ .con≡ = λ _ → ≡.refl
  refl≡ʳ .ty≡ = λ _ _ → ≡.refl

  symRec≡ : {r s : Hom A B} → r ≡ʳ s → s ≡ʳ r
  symRec≡ p .con≡ Γ =
    ≡.sym (p .con≡ Γ)
  symRec≡ p .ty≡ Γ A =
    ≡.symʰ (B.Tyᴬ (symRec≡ p)) (p .con≡ Γ) (p .ty≡ Γ A)

  transRec≡ : {r s t : Hom A B}
            → r ≡ʳ s → s ≡ʳ t → r ≡ʳ t
  transRec≡ p q .con≡ Γ =
    ≡.trans (p .con≡ Γ) (q .con≡ Γ)
  transRec≡ p q .ty≡ Γ A =
    ≡.transʰ (B.Tyᴬ (transRec≡ p q)) (p .con≡ Γ) (q .con≡ Γ) (p .ty≡ Γ A) (q .ty≡ Γ A)

idʳ : ∀ {A : Algebra} → Hom A A
idʳ {A} = record
  { conʳ = λ Γ → Γ
  ; tyʳ = λ A → A
  ; ∙ʳ = ≡.refl
  ; ▷ʳ = ≡.refl
  ; ιʳ = ≡.refl
  ; πʳ = ≡.refl }


module _ {A B C : Algebra} (g : Hom B C) (f : Hom A B) where

  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  module f = Hom f
  module g = Hom g
  open ≡-Reasoning
  open Hom
  mutual
    _∘ʳ_ : Hom A C
    q : ∀ Γ A B
      → g.tyʳ (g.A.πᴬ Γ A B)
      ≡ C.πᴬ (g.conʳ Γ) (g.tyʳ A)
            (subst C.Tyᴬ g.▷ʳ (g.tyʳ B))
    q Γ A B = g.πʳ
    p : ∀ Γ A B
      → g.tyʳ (g.A.πᴬ (f.conʳ Γ) (f.tyʳ A)
                      (subst B.Tyᴬ (▷ʳ {!g!}) (f.tyʳ B)))
      ≡ g.B.πᴬ (g.conʳ (f.conʳ Γ))
                (g.tyʳ (f.tyʳ A))
                (subst g.B.Tyᴬ {!!} (g.tyʳ (f.tyʳ B)))

    _∘ʳ_ .conʳ = λ Γ → g.conʳ (f.conʳ Γ)            
    _∘ʳ_ .tyʳ = λ A → g.tyʳ (f.tyʳ A)
    _∘ʳ_ .∙ʳ = ≡.trans (≡.cong g.conʳ f.∙ʳ) g.∙ʳ
    _∘ʳ_ .▷ʳ = ≡.trans (≡.cong g.conʳ f.▷ʳ) g.▷ʳ
    _∘ʳ_ .ιʳ = ≡.trans (≡.cong g.tyʳ f.ιʳ) g.ιʳ
    _∘ʳ_ .πʳ {Γ} {At} {Bt} =
      ≡.trans (≡.cong g.tyʳ f.πʳ) (p Γ At Bt)


    p Γ A B =
      begin
      g.tyʳ (B.πᴬ {!f.conʳ Γ!} {!f.tyʳ A!}
                  {!subst B.Tyᴬ _ (f.tyʳ B)!})
        ≡⟨ q (f.conʳ Γ) (f.tyʳ A)
            (subst B.Tyᴬ _ (f.tyʳ B)) ⟩
      C.πᴬ (g.conʳ (f.conʳ Γ))
            (g.tyʳ (f.tyʳ A))
            (subst C.Tyᴬ _ (g.tyʳ (subst B.Tyᴬ _ (f.tyʳ B))))
        ≡⟨ cong (C.πᴬ (g.conʳ (f.conʳ Γ)) (g.tyʳ (f.tyʳ A))) {!cong !} ⟩
      C.πᴬ (g.conʳ (f.conʳ Γ))
          (g.tyʳ (f.tyʳ A))
          (subst C.Tyᴬ _ (g.tyʳ (f.tyʳ B))) ∎


-- AlgebraComp {A} {B} r f = record
--   { conʳ = λ Γ → f.conʰ (r.conʳ Γ)
--   ; tyʳ = λ A → f.tyʰ (r.tyʳ A)
--   ; ∙ʳ = ≡.trans (≡.cong f.conʰ r.∙ʳ) f.∙ʰ
--   ; ▷ʳ = ≡.trans (≡.cong f.conʰ r.▷ʳ) f.▷ʰ
--   ; ιʳ = ≡.trans (≡.cong f.tyʰ r.ιʳ) f.ιʰ
--   ; πʳ = λ {Γ A B} → ≡.trans (≡.cong f.tyʰ r.πʳ) w }
--   where
--   module A = Algebra A
--   module B = Algebra B
--   module r = Rec r
--   module f = AlgebraHom f
--   -- w : ∀ {Γ A B}
--   --   → f.tyʰ (f.A.πᴬ (r.conʳ Γ) (r.tyʳ A)
--   --           (subst f.A.Tyᴬ r.▷ʳ (r.tyʳ B)))
--   --   ≡ f.B.πᴬ (f.conʰ (r.conʳ Γ)) (f.tyʰ (r.tyʳ A))
--   --             (subst f.B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ʳ) f.▷ʰ) (f.tyʰ (r.tyʳ B)))
--   -- w {Γ} {A} {B} =
--   --   f.tyʰ (A.πᴬ (r.conʳ Γ) (r.tyʳ A) (subst A.Tyᴬ r.▷ʳ (r.tyʳ B)))
--   --     ≡⟨ f.πʰ ⟩
--   --   B.πᴬ (f.conʰ (r.conʳ Γ)) (f.tyʰ (r.tyʳ A))
--   --         (subst B.Tyᴬ f.▷ʰ (f.tyʰ (subst A.Tyᴬ r.▷ʳ (r.tyʳ B))))
--   --     ≡⟨ ≡.cong (B.πᴬ (f.conʰ (r.conʳ Γ)) (f.tyʰ (r.tyʳ A))) q ⟩
--   --   B.πᴬ (f.conʰ (r.conʳ Γ)) (f.tyʰ (r.tyʳ A))
--   --         (subst B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ʳ) f.▷ʰ) (f.tyʰ (r.tyʳ B))) ∎
--   --   where
--   --   open ≡.≡-Reasoning
--   --   q : subst B.Tyᴬ f.▷ʰ (f.tyʰ (subst A.Tyᴬ r.▷ʳ (r.tyʳ B)))
--   --     ≡ subst B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ʳ) f.▷ʰ) (f.tyʰ (r.tyʳ B))
--   --   q =
--   --     subst B.Tyᴬ f.▷ʰ (f.tyʰ (subst A.Tyᴬ r.▷ʳ (r.tyʳ B)))
--   --       ≡⟨ ≡.cong (subst B.Tyᴬ f.▷ʰ) (tyʰ-subst f r.▷ʳ (r.tyʳ B)) ⟩
--   --     subst B.Tyᴬ f.▷ʰ (subst B.Tyᴬ (≡.cong f.conʰ r.▷ʳ) (f.tyʰ (r.tyʳ B))) 
--   --       ≡⟨ ≡.subst-subst {P = B.Tyᴬ} (≡.cong f.conʰ r.▷ʳ) {f.▷ʰ} ⟩
--   --     subst B.Tyᴬ (≡.trans (≡.cong f.conʰ r.▷ʳ) f.▷ʰ) (f.tyʰ (r.tyʳ B)) ∎

-- _∘ʳ_ {A} {B} {C} g f = record
--   { conʳ = λ Γ → g.conʳ (f.conʳ Γ)
--   ; tyʳ = λ A → g.tyʳ (f.tyʳ A)
--   ; ∙ʳ = ≡.trans (≡.cong g.conʳ f.∙ʳ) g.∙ʳ
--   ; ▷ʳ = ≡.trans (≡.cong g.conʳ f.▷ʳ) g.▷ʳ
--   ; ιʳ = ≡.trans (≡.cong g.tyʳ f.ιʳ) g.ιʳ
--   ; πʳ = λ {Γ} {A} {B} →
--       ≡.trans (≡.cong g.tyʳ f.πʳ) (p Γ A B) }
--   where
