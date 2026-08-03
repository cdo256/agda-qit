open import QIT.Prelude

module QIT.Examples.ConTy.DirectMutualProjectionEquiv
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.Prelude
open import QIT.Prop

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.MutualProjection as M
open import QIT.Category.Base
open import QIT.Functor.Base

F₀ : D.Algebra ℓA → M.Algebra ℓA
F₀ {ℓA} DA = record
  { Con = Con
  ; Ty = Ty
  ; ty₁ = ty₁
  ; ∙ = DA.∙
  ; ▷ = λ γ a a₁ → γ DA.▷ mkTy a a₁
  ; u = λ γ → γ , DA.u γ
  ; u₁ = λ γ → refl
  ; π = λ γ a b a₁ b₁ → γ , DA.π γ (mkTy a a₁) (mkTy b b₁)
  ; π₁ = λ γ a b a₁ b₁ → refl
  ; σ = λ γ a b a₁ b₁ → γ , DA.σ γ (mkTy a a₁) (mkTy b b₁)
  ; σ₁ = λ γ a b a₁ b₁ → refl
  ; σ▷ = λ γ a b a₁ b₁ → DA.σ▷ γ (mkTy a a₁) (mkTy b b₁)
  ; σπ = λ γ a b c a₁ b₁ c₁ →
      cong (γ ,_)
        (trans
          (DA.σπ γ (mkTy a a₁) (mkTy b b₁) (mkTy c c₁))
          (cong
            (DA.π γ (DA.σ γ (mkTy a a₁) (mkTy b b₁)))
            (subst-subst DA.Ty c₁ (DA.σ▷ γ (mkTy a a₁) (mkTy b b₁)) (proj₂ c))))
  }
  module F₀ where
  open ≡
  module DA = D.Algebra DA
  Con : Set ℓA
  Con = DA.Con
  Ty : Set ℓA
  Ty = Σ Con DA.Ty
  ty₁ : Ty → Con
  ty₁ = proj₁
  mkTy : ∀ {γ} → (a : Ty) → (ty₁ a ≡ γ) → DA.Ty γ
  mkTy a a₁ = subst DA.Ty a₁ (proj₂ a)


F₁ : ∀ {A : D.Algebra ℓA} {B : D.Algebra ℓB}
   → D.Hom A B → M.Hom (F₀ A) (F₀ B)
F₁ {A = A} {B} f = record
  { conᴿ = f.conᴿ
  ; tyᴿ = tyᴿ
  ; ty₁ᴿ = λ _ → refl
  ; ∙ᴿ = f.∙ᴿ
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = λ γ → Σ≡ refl (f.uᴿ γ)
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ
  }
  module F₁ where
  open ≡
  module A = D.Algebra A
  module B = D.Algebra B
  module FA = M.Algebra (F₀ A)
  module FB = M.Algebra (F₀ B)
  module f = D.Hom f

  tyᴿ : FA.Ty → FB.Ty
  tyᴿ (γ , a) = f.conᴿ γ , f.tyᴿ γ a

  mkTy-natural≡ : ∀ {γ} (a : FA.Ty)
    → (a₁ : FA.ty₁ a ≡ γ)
    → (a₁' : FB.ty₁ (tyᴿ a) ≡ f.conᴿ γ)
    → subst B.Ty a₁' (proj₂ (tyᴿ a)) ≡ f.tyᴿ γ (subst A.Ty a₁ (proj₂ a))
  mkTy-natural≡ (δ , a) a₁ a₁' =
    trans
      (subst-irrel (cong f.conᴿ a₁) a₁' (f.tyᴿ δ a))
      (sym (D.tyᴿ-subst f a₁ a))

  subst-▷ : ∀ {γ} {x y : B.Ty (f.conᴿ γ)}
    → (p : x ≡ y)
    → (u : B.Ty (f.conᴿ γ B.▷ x))
    → subst (λ z → B.Ty (f.conᴿ γ B.▷ z)) p u
    ≡ subst B.Ty (cong (λ z → f.conᴿ γ B.▷ z) p) u
  subst-▷ refl u = refl

  ▷ᴿ : ∀ γ a
    → (a₁ : FA.ty₁ a ≡ γ)
    → (a₁' : FB.ty₁ (tyᴿ a) ≡ f.conᴿ γ)
    → f.conᴿ (FA.▷ γ a a₁) ≡ FB.▷ (f.conᴿ γ) (tyᴿ a) a₁'
  ▷ᴿ γ a a₁ a₁' =
    trans
      (f.▷ᴿ γ (subst A.Ty a₁ (proj₂ a)))
      (cong (λ x → f.conᴿ γ B.▷ x) (sym (mkTy-natural≡ a a₁ a₁')))

  πᴿ : ∀ γ a b
    → (a₁ : FA.ty₁ a ≡ γ)
    → (b₁ : FA.ty₁ b ≡ FA.▷ γ a a₁)
    → (a₁' : FB.ty₁ (tyᴿ a) ≡ f.conᴿ γ)
    → (b₁' : FB.ty₁ (tyᴿ b) ≡ FB.▷ (f.conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (FA.π γ a b a₁ b₁) ≡ FB.π (f.conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  πᴿ γ (δ , a) (ε , b) a₁ b₁ a₁' b₁' = Σ≡ ≡.refl p
    where
    open ≡.≡-Reasoning
    a* : A.Ty γ
    a* = subst A.Ty a₁ a
    b* : A.Ty (γ A.▷ a*)
    b* = subst A.Ty b₁ b
    a*' : B.Ty (f.conᴿ γ)
    a*' = subst B.Ty a₁' (f.tyᴿ δ a)
    pA : a*' ≡ f.tyᴿ γ a*
    pA = mkTy-natural≡ (δ , a) a₁ a₁'
    qA : f.conᴿ γ B.▷ f.tyᴿ γ a* ≡ f.conᴿ γ B.▷ a*'
    qA = cong (λ x → f.conᴿ γ B.▷ x) (sym pA)
    lhsB : B.Ty (f.conᴿ (γ A.▷ a*))
    lhsB = f.tyᴿ (γ A.▷ a*) b*
    pB₀ : subst B.Ty qA (subst B.Ty (f.▷ᴿ γ a*) lhsB) ≡ subst B.Ty b₁' (f.tyᴿ ε b)
    pB₀ =
      subst B.Ty qA (subst B.Ty (f.▷ᴿ γ a*) lhsB)
        ≡⟨ cong (subst B.Ty qA) (cong (subst B.Ty (f.▷ᴿ γ a*)) (D.tyᴿ-subst f b₁ b)) ⟩
      subst B.Ty qA (subst B.Ty (f.▷ᴿ γ a*) (subst B.Ty (cong f.conᴿ b₁) (f.tyᴿ ε b)))
        ≡⟨ cong (subst B.Ty qA) (subst-subst B.Ty (cong f.conᴿ b₁) (f.▷ᴿ γ a*) (f.tyᴿ ε b)) ⟩
      subst B.Ty qA (subst B.Ty (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) (f.tyᴿ ε b))
        ≡⟨ subst-subst B.Ty (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) qA (f.tyᴿ ε b) ⟩
      subst B.Ty (trans (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) qA) (f.tyᴿ ε b)
        ≡⟨ subst-irrel (trans (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) qA) b₁' (f.tyᴿ ε b) ⟩
      subst B.Ty b₁' (f.tyᴿ ε b) ∎
    pB : subst (λ z → B.Ty (f.conᴿ γ B.▷ z)) (sym pA) (subst B.Ty (f.▷ᴿ γ a*) lhsB)
       ≡ subst B.Ty b₁' (f.tyᴿ ε b)
    pB = trans (subst-▷ (sym pA) (subst B.Ty (f.▷ᴿ γ a*) lhsB)) pB₀
    p : f.tyᴿ γ (A.π γ a* b*) ≡ B.π (f.conᴿ γ) a*' (subst B.Ty b₁' (f.tyᴿ ε b))
    p =
      f.tyᴿ γ (A.π γ a* b*)
        ≡⟨ f.πᴿ γ a* b* ⟩
      B.π (f.conᴿ γ) (f.tyᴿ γ a*) (subst B.Ty (f.▷ᴿ γ a*) lhsB)
        ≡⟨ dcong₂ (B.π (f.conᴿ γ)) (sym pA) pB ⟩
      B.π (f.conᴿ γ) a*' (subst B.Ty b₁' (f.tyᴿ ε b)) ∎

  σᴿ : ∀ γ a b
    → (a₁ : FA.ty₁ a ≡ γ)
    → (b₁ : FA.ty₁ b ≡ FA.▷ γ a a₁)
    → (a₁' : FB.ty₁ (tyᴿ a) ≡ f.conᴿ γ)
    → (b₁' : FB.ty₁ (tyᴿ b) ≡ FB.▷ (f.conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (FA.σ γ a b a₁ b₁) ≡ FB.σ (f.conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  σᴿ γ (δ , a) (ε , b) a₁ b₁ a₁' b₁' = Σ≡ ≡.refl p
    where
    open ≡.≡-Reasoning
    a* : A.Ty γ
    a* = subst A.Ty a₁ a
    b* : A.Ty (γ A.▷ a*)
    b* = subst A.Ty b₁ b
    a*' : B.Ty (f.conᴿ γ)
    a*' = subst B.Ty a₁' (f.tyᴿ δ a)
    pA : a*' ≡ f.tyᴿ γ a*
    pA = mkTy-natural≡ (δ , a) a₁ a₁'
    qA : f.conᴿ γ B.▷ f.tyᴿ γ a* ≡ f.conᴿ γ B.▷ a*'
    qA = cong (λ x → f.conᴿ γ B.▷ x) (sym pA)
    lhsB : B.Ty (f.conᴿ (γ A.▷ a*))
    lhsB = f.tyᴿ (γ A.▷ a*) b*
    pB₀ : subst B.Ty qA (subst B.Ty (f.▷ᴿ γ a*) lhsB) ≡ subst B.Ty b₁' (f.tyᴿ ε b)
    pB₀ =
      subst B.Ty qA (subst B.Ty (f.▷ᴿ γ a*) lhsB)
        ≡⟨ cong (subst B.Ty qA) (cong (subst B.Ty (f.▷ᴿ γ a*)) (D.tyᴿ-subst f b₁ b)) ⟩
      subst B.Ty qA (subst B.Ty (f.▷ᴿ γ a*) (subst B.Ty (cong f.conᴿ b₁) (f.tyᴿ ε b)))
        ≡⟨ cong (subst B.Ty qA) (subst-subst B.Ty (cong f.conᴿ b₁) (f.▷ᴿ γ a*) (f.tyᴿ ε b)) ⟩
      subst B.Ty qA (subst B.Ty (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) (f.tyᴿ ε b))
        ≡⟨ subst-subst B.Ty (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) qA (f.tyᴿ ε b) ⟩
      subst B.Ty (trans (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) qA) (f.tyᴿ ε b)
        ≡⟨ subst-irrel (trans (trans (cong f.conᴿ b₁) (f.▷ᴿ γ a*)) qA) b₁' (f.tyᴿ ε b) ⟩
      subst B.Ty b₁' (f.tyᴿ ε b) ∎
    pB : subst (λ z → B.Ty (f.conᴿ γ B.▷ z)) (sym pA) (subst B.Ty (f.▷ᴿ γ a*) lhsB)
       ≡ subst B.Ty b₁' (f.tyᴿ ε b)
    pB = trans (subst-▷ (sym pA) (subst B.Ty (f.▷ᴿ γ a*) lhsB)) pB₀
    p : f.tyᴿ γ (A.σ γ a* b*) ≡ B.σ (f.conᴿ γ) a*' (subst B.Ty b₁' (f.tyᴿ ε b))
    p =
      f.tyᴿ γ (A.σ γ a* b*)
        ≡⟨ f.σᴿ γ a* b* ⟩
      B.σ (f.conᴿ γ) (f.tyᴿ γ a*) (subst B.Ty (f.▷ᴿ γ a*) lhsB)
        ≡⟨ dcong₂ (B.σ (f.conᴿ γ)) (sym pA) pB ⟩
      B.σ (f.conᴿ γ) a*' (subst B.Ty b₁' (f.tyᴿ ε b)) ∎


F : Functor (D.Cat ℓA) (M.Cat ℓA)
F = record
  { ob = λ A → F₀ A
  ; hom = λ f → F₁ f
  ; id = M.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; comp = λ f g → M.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; resp = λ p → M.mk≈ (D.con≡ p) λ { (γ , a) → Σ≡ (D.con≡ p γ) (D.ty≡ p γ a) }
  }

G₀ : M.Algebra ℓA → D.Algebra ℓA
G₀ {ℓA} MA = record
  { Con = Con
  ; Ty = Ty
  ; ∙ = MA.∙
  ; _▷_ = λ γ (a , a₁) → MA.▷ γ a a₁
  ; u = λ γ → MA.u γ , MA.u₁ γ
  ; π = λ γ (a , a₁) (b , b₁) → MA.π γ a b a₁ b₁ , MA.π₁ γ a b a₁ b₁
  ; σ = λ γ (a , a₁) (b , b₁) → MA.σ γ a b a₁ b₁ , MA.σ₁ γ a b a₁ b₁
  ; σ▷ = λ γ (a , a₁) (b , b₁) → MA.σ▷ γ a b a₁ b₁
  ; σπ = λ γ (a , a₁) (b , b₁) (c , c₁) →
      trans
        (ΣP≡ _ _ (MA.σπ γ a b c a₁ b₁ c₁))
        (cong (h γ a b a₁ b₁) (sym (q γ a b c a₁ b₁ c₁)))
  }
  module G₀ where
  open ≡
  module MA = M.Algebra MA
  open MA using (ty₁)
  Con : Set ℓA
  Con = MA.Con
  Ty : Con → Set ℓA
  Ty γ = ΣP MA.Ty λ a → ty₁ a ≡ γ

  Ty-fst : ∀ {γ δ : Con} {a : Ty γ} → (r : γ ≡ δ) → subst Ty r a .fst ≡ a .fst
  Ty-fst refl = refl

  h : ∀ γ a b
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ MA.▷ γ a a₁)
    → Ty (MA.▷ γ (MA.σ γ a b a₁ b₁) (MA.σ₁ γ a b a₁ b₁))
    → Ty γ
  h γ a b a₁ b₁ (c , c₁) =
    MA.π γ (MA.σ γ a b a₁ b₁) c (MA.σ₁ γ a b a₁ b₁) c₁ ,
    MA.π₁ γ (MA.σ γ a b a₁ b₁) c (MA.σ₁ γ a b a₁ b₁) c₁

  q : ∀ γ a b c
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ MA.▷ γ a a₁)
    → (c₁ : ty₁ c ≡ MA.▷ (MA.▷ γ a a₁) b b₁)
    → subst Ty (MA.σ▷ γ a b a₁ b₁) (c , c₁)
      ≡ (c , trans c₁ (MA.σ▷ γ a b a₁ b₁))
  q γ a b c a₁ b₁ c₁ =
    ΣP≡ _ _
      (trans
        (cong fst (subst-ΣP (λ δ x → ty₁ x ≡ δ) (MA.σ▷ γ a b a₁ b₁) (c , c₁)))
        (subst-const MA.Ty c (MA.σ▷ γ a b a₁ b₁)))

G₁ : ∀ {A : M.Algebra ℓA} {B : M.Algebra ℓB}
   → M.Hom A B → D.Hom (G₀ A) (G₀ B)
G₁ {A = A} {B} f = record
  { conᴿ = f.conᴿ
  ; tyᴿ = tyᴿ
  ; ∙ᴿ = f.∙ᴿ
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ
  }
  module G₁ where
  open ≡
  module A = M.Algebra A
  module B = M.Algebra B
  module GA = D.Algebra (G₀ A)
  module GB = D.Algebra (G₀ B)
  module f = M.Hom f
  open ≡.≡-Reasoning

  tyᴿ : (γ : GA.Con) → GA.Ty γ → GB.Ty (f.conᴿ γ)
  tyᴿ γ (a , a₁) = f.tyᴿ a , trans (f.ty₁ᴿ a) (cong f.conᴿ a₁)

  Ty-fst : ∀ {γ δ : GB.Con} {a : GB.Ty γ} → (r : γ ≡ δ) → subst GB.Ty r a .fst ≡ a .fst
  Ty-fst refl = refl

  ∙ᴿ : f.conᴿ GA.∙ ≡ GB.∙
  ∙ᴿ = f.∙ᴿ

  ▷ᴿ : ∀ γ a → f.conᴿ (GA._▷_ γ a) ≡ GB._▷_ (f.conᴿ γ) (tyᴿ γ a)
  ▷ᴿ γ (a , a₁) = f.▷ᴿ γ a a₁ (trans (f.ty₁ᴿ a) (cong f.conᴿ a₁))

  uᴿ : ∀ γ → tyᴿ γ (GA.u γ) ≡ GB.u (f.conᴿ γ)
  uᴿ γ = ΣP≡ _ _ (f.uᴿ γ)

  πᴿ : ∀ γ a b → tyᴿ γ (GA.π γ a b)
    ≡ GB.π (f.conᴿ γ) (tyᴿ γ a) (subst GB.Ty (▷ᴿ γ a) (tyᴿ (GA._▷_ γ a) b))
  πᴿ γ (a , a₁) (b , b₁) = ΣP≡ _ _ p
    where
    a₁' : B.ty₁ (f.tyᴿ a) ≡ f.conᴿ γ
    a₁' = trans (f.ty₁ᴿ a) (cong f.conᴿ a₁)
    tb : GB.Ty (GB._▷_ (f.conᴿ γ) (tyᴿ γ (a , a₁)))
    tb = subst GB.Ty (▷ᴿ γ (a , a₁)) (tyᴿ (GA._▷_ γ (a , a₁)) (b , b₁))
    b₁' : B.ty₁ (f.tyᴿ b) ≡ B.▷ (f.conᴿ γ) (f.tyᴿ a) a₁'
    b₁' = trans (trans (f.ty₁ᴿ b) (cong f.conᴿ b₁)) (f.▷ᴿ γ a a₁ a₁')
    b₁'' : B.ty₁ (tb .fst) ≡ B.▷ (f.conᴿ γ) (f.tyᴿ a) a₁'
    b₁'' = substp (λ x → B.ty₁ x ≡ B.▷ (f.conᴿ γ) (f.tyᴿ a) a₁') (sym (Ty-fst (▷ᴿ γ (a , a₁)))) b₁'
    p : f.tyᴿ (A.π γ a b a₁ b₁)
      ≡ B.π (f.conᴿ γ) (f.tyᴿ a) (tb .fst) a₁' b₁''
    p =
      f.tyᴿ (A.π γ a b a₁ b₁)
        ≡⟨ f.πᴿ γ a b a₁ b₁ a₁' b₁' ⟩
      B.π (f.conᴿ γ) (f.tyᴿ a) (f.tyᴿ b) a₁' b₁'
        ≡⟨ dcongsp (λ x p → B.π (f.conᴿ γ) (f.tyᴿ a) x a₁' p) (sym (Ty-fst (▷ᴿ γ (a , a₁)))) ⟩
      B.π (f.conᴿ γ) (f.tyᴿ a) (tb .fst) a₁' b₁'' ∎

  σᴿ : ∀ γ a b → tyᴿ γ (GA.σ γ a b)
    ≡ GB.σ (f.conᴿ γ) (tyᴿ γ a) (subst GB.Ty (▷ᴿ γ a) (tyᴿ (GA._▷_ γ a) b))
  σᴿ γ (a , a₁) (b , b₁) = ΣP≡ _ _ p
    where
    a₁' : B.ty₁ (f.tyᴿ a) ≡ f.conᴿ γ
    a₁' = trans (f.ty₁ᴿ a) (cong f.conᴿ a₁)
    tb : GB.Ty (GB._▷_ (f.conᴿ γ) (tyᴿ γ (a , a₁)))
    tb = subst GB.Ty (▷ᴿ γ (a , a₁)) (tyᴿ (GA._▷_ γ (a , a₁)) (b , b₁))
    b₁' : B.ty₁ (f.tyᴿ b) ≡ B.▷ (f.conᴿ γ) (f.tyᴿ a) a₁'
    b₁' = trans (trans (f.ty₁ᴿ b) (cong f.conᴿ b₁)) (f.▷ᴿ γ a a₁ a₁')
    b₁'' : B.ty₁ (tb .fst) ≡ B.▷ (f.conᴿ γ) (f.tyᴿ a) a₁'
    b₁'' = substp (λ x → B.ty₁ x ≡ B.▷ (f.conᴿ γ) (f.tyᴿ a) a₁') (sym (Ty-fst (▷ᴿ γ (a , a₁)))) b₁'
    p : f.tyᴿ (A.σ γ a b a₁ b₁)
      ≡ B.σ (f.conᴿ γ) (f.tyᴿ a) (tb .fst) a₁' b₁''
    p =
      f.tyᴿ (A.σ γ a b a₁ b₁)
        ≡⟨ f.σᴿ γ a b a₁ b₁ a₁' b₁' ⟩
      B.σ (f.conᴿ γ) (f.tyᴿ a) (f.tyᴿ b) a₁' b₁'
        ≡⟨ dcongsp (λ x p → B.σ (f.conᴿ γ) (f.tyᴿ a) x a₁' p) (sym (Ty-fst (▷ᴿ γ (a , a₁)))) ⟩
      B.σ (f.conᴿ γ) (f.tyᴿ a) (tb .fst) a₁' b₁'' ∎

G : Functor (M.Cat ℓA) (D.Cat ℓA)
G = record
  { ob = λ A → G₀ A
  ; hom = λ f → G₁ f
  ; id = D.mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; comp = λ f g → D.mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  ; resp = resp
  }
  where
  Ty-fst : ∀ {A : M.Algebra ℓA} {γ δ : D.Con (G₀ A)} {a : D.Ty (G₀ A) γ}
    → (r : γ ≡ δ) → subst (D.Ty (G₀ A)) r a .fst ≡ a .fst
  Ty-fst ≡.refl = ≡.refl

  resp : ∀ {X Y : M.Algebra ℓA} {f g : M.Hom X Y}
       → f M.≈ g → G₁ f D.≈ G₁ g
  resp {Y = Y} p = D.mk≈ (M.con≡ p) λ γ a → ΣP≡ _ _ (≡.trans (Ty-fst {A = Y} (M.con≡ p γ)) (M.ty≡ p (a .fst)))


open import QIT.Category.Equivalence
open import QIT.Functor.NatTrans
open import QIT.Functor.Properties
open import QIT.Category.Morphism

η : NatIso {C = D.Cat ℓA} {D = D.Cat ℓA} Id (G ∘ꟳ F)
η {ℓA} = record
  { ob = η₀
  ; hom = η₁
  ; isIso = isIso-η }
  where
  η⁻₀ : (A : D.Algebra ℓA) → D.Cat ℓA [ G₀ (F₀ A) , A ]
  η⁻₀ A = record
    { conᴿ = conᴿ
    ; tyᴿ = tyᴿ
    ; ∙ᴿ = ≡.refl
    ; ▷ᴿ = λ _ _ → ≡.refl
    ; uᴿ = λ _ → ≡.refl
    ; πᴿ = λ _ _ _ → ≡.refl
    ; σᴿ = λ _ _ _ → ≡.refl }
    module η⁻₀ where
    module A = D.Algebra A
    module FA = M.Algebra (F₀ A)
    module F₀A = F₀ A
    module GFA = D.Algebra (G₀ (F₀ A))
    module G₀FA = G₀ (F₀ A)
    conᴿ : GFA.Con → A.Con
    conᴿ γ = γ
    tyᴿ : (γ : GFA.Con) → GFA.Ty γ → A.Ty (conᴿ γ)
    tyᴿ γ ((γ' , a) , a₁) = subst A.Ty a₁ a
  η₀ : (A : D.Algebra ℓA) → D.Cat ℓA [ A , G₀ (F₀ A) ]
  η₀ A = record
    { conᴿ = conᴿ
    ; tyᴿ = tyᴿ
    ; ∙ᴿ = ≡.refl
    ; ▷ᴿ = λ _ _ → ≡.refl
    ; uᴿ = λ _ → ≡.refl
    ; πᴿ = λ _ _ _ → ≡.refl
    ; σᴿ = λ _ _ _ → ≡.refl }
    module η₀ where
    module A = D.Algebra A
    module FA = M.Algebra (F₀ A)
    module F₀A = F₀ A
    module GFA = D.Algebra (G₀ (F₀ A))
    module G₀FA = G₀ (F₀ A)
    conᴿ : A.Con → GFA.Con
    conᴿ γ = γ
    tyᴿ : (γ : A.Con) → A.Ty γ → GFA.Ty (conᴿ γ)
    tyᴿ γ a = (γ , a) , ≡.refl
  η₁ : {A B : D.Algebra ℓA} (f : D.Hom A B)
    →   G₁ (F₁ f) D.∘ (η₀ A)
    D.≈ η₀ B D.∘ f
  η₁ {A} {B} f = D.mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  isIso-η : ∀ A → IsIso (D.Cat ℓA) (η₀ A)
  isIso-η A = record
    { f⁻¹ = η⁻₀ A
    ; linv = D.mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
    ; rinv = D.mk≈ (λ _ → ≡.refl) p }
    where
    module A = D.Algebra A
    module FA = M.Algebra (F₀ A)
    module F₀A = F₀ A
    module GFA = D.Algebra (G₀ (F₀ A))
    module G₀FA = G₀ (F₀ A)
    open ≡.≡-Reasoning
    open ≡
    p : (γ : GFA.Con) (a : GFA.Ty γ)
      → η₀.tyᴿ A (η⁻₀.conᴿ A γ) (η⁻₀.tyᴿ A γ a) ≡ a
    p γ ((γ' , a) , a₁) =
      ΣP≡ _ _ q
      where
      q : η₀.tyᴿ A (η⁻₀.conᴿ A γ) (η⁻₀.tyᴿ A γ ((γ' , a) , a₁)) .fst ≡ (γ' , a)
      q = Σ≡ (sym a₁) (subst-inv A.Ty a₁)

ε : NatIso {C = M.Cat ℓA} {D = M.Cat ℓA} (F ∘ꟳ G) Id
ε {ℓA} = record
  { ob = ε₀
  ; hom = ε₁
  ; isIso = isIso-ε }
  where
  ε⁻₀ : (A : M.Algebra ℓA) → M.Cat ℓA [ A , F₀ (G₀ A) ]
  ε⁻₀ A = record
    { conᴿ = conᴿ
    ; tyᴿ = tyᴿ
    ; ty₁ᴿ = ty₁ᴿ
    ; ∙ᴿ = ∙ᴿ
    ; ▷ᴿ = ▷ᴿ
    ; uᴿ = uᴿ
    ; πᴿ = πᴿ
    ; σᴿ = σᴿ
    }
    module ε⁻₀ where
    module A = M.Algebra A
    module GA = D.Algebra (G₀ A)
    module G₀A = G₀ A
    module FGA = M.Algebra (F₀ (G₀ A))
    module F₀G₀A = F₀ (G₀ A)
    open ≡.≡-Reasoning

    conᴿ : A.Con → FGA.Con
    conᴿ γ = γ
    tyᴿ : A.Ty → FGA.Ty
    tyᴿ a = A.ty₁ a , a , ≡.refl
    ty₁ᴿ : ∀ a → FGA.ty₁ (tyᴿ a) ≡ conᴿ (A.ty₁ a)
    ty₁ᴿ a = ≡.refl

    ∙ᴿ : conᴿ A.∙ ≡ FGA.∙
    ∙ᴿ = ≡.refl
    ▷ᴿ : ∀ γ a
      → (a₁ : A.ty₁ a ≡ γ)
      → (a₁' : FGA.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → conᴿ (A.▷ γ a a₁) ≡ FGA.▷ (conᴿ γ) (tyᴿ a) a₁'
    ▷ᴿ γ a a₁ a₁' =
      dcongsp (A.▷ γ) p
      where
      open ≡.≡-Reasoning
      p : a ≡ subst GA.Ty a₁ (a , ≡.refl) .fst
      p = ≡.sym (G₀.Ty-fst A a₁)

    uᴿ : ∀ γ → tyᴿ (A.u γ) ≡ FGA.u (conᴿ γ)
    uᴿ γ = Σ≡ (A.u₁ γ) (ΣP≡ _ _ p)
      where
      p : subst G₀A.Ty (A.u₁ γ) (A.u γ , ≡.refl) .fst
        ≡ A.u γ 
      p = G₀A.Ty-fst (A.u₁ γ)

    πᴿ : ∀ γ a b
      → (a₁ : A.ty₁ a ≡ γ)
      → (b₁ : A.ty₁ b ≡ A.▷ γ a a₁)
      → (a₁' : FGA.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → (b₁' : FGA.ty₁ (tyᴿ b) ≡ FGA.▷ (conᴿ γ) (tyᴿ a) a₁')
      → tyᴿ (A.π γ a b a₁ b₁)
      ≡ FGA.π (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
    πᴿ γ a b a₁ b₁ a₁' b₁' = Σ≡ (A.π₁ γ a b a₁ b₁) (ΣP≡ _ _ p)
      where
      pa : subst GA.Ty a₁' (a , ≡.refl) .fst ≡ a
      pa = G₀A.Ty-fst a₁'

      pb : subst (λ _ → A.Ty) (≡.sym pa) b
         ≡ subst GA.Ty b₁' (b , ≡.refl) .fst
      pb = ≡.trans
             (≡.subst-const A.Ty b (≡.sym pa))
             (≡.sym (G₀A.Ty-fst b₁'))

      p : subst GA.Ty (A.π₁ γ a b a₁ b₁)
           (A.π γ a b a₁ b₁ , ≡.refl) .fst
           ≡
           GA.π (conᴿ γ) (F₀G₀A.mkTy (tyᴿ a) a₁')
           (F₀G₀A.mkTy (tyᴿ b) b₁') .fst
      p =
        subst GA.Ty (A.π₁ γ a b a₁ b₁)
          (A.π γ a b a₁ b₁ , ≡.refl) .fst
          ≡⟨ G₀A.Ty-fst (A.π₁ γ a b a₁ b₁) ⟩
        A.π γ a b a₁ b₁
          ≡⟨ ≡.dcongsspp (A.π γ) (≡.sym pa) pb ⟩
        A.π γ (subst GA.Ty a₁' (a , ≡.refl) .fst)
              (subst GA.Ty b₁' (b , ≡.refl) .fst)
              (subst GA.Ty a₁' (a , ≡.refl) .snd)
              (subst GA.Ty b₁' (b , ≡.refl) .snd)
          ≡⟨ ≡.refl ⟩
        GA.π (conᴿ γ) (F₀G₀A.mkTy (tyᴿ a) a₁')
           (F₀G₀A.mkTy (tyᴿ b) b₁') .fst ∎

    σᴿ : ∀ γ a b
      → (a₁ : A.ty₁ a ≡ γ)
      → (b₁ : A.ty₁ b ≡ A.▷ γ a a₁)
      → (a₁' : FGA.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → (b₁' : FGA.ty₁ (tyᴿ b) ≡ FGA.▷ (conᴿ γ) (tyᴿ a) a₁')
      → tyᴿ (A.σ γ a b a₁ b₁)
      ≡ FGA.σ (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
    σᴿ γ a b a₁ b₁ a₁' b₁' = Σ≡ (A.σ₁ γ a b a₁ b₁) (ΣP≡ _ _ p)
      where
      pa : subst GA.Ty a₁' (a , ≡.refl) .fst ≡ a
      pa = G₀A.Ty-fst a₁'

      pb : subst (λ _ → A.Ty) (≡.sym pa) b ≡ subst GA.Ty b₁' (b , ≡.refl) .fst
      pb = ≡.trans
             (≡.subst-const A.Ty b (≡.sym pa))
             (≡.sym (G₀A.Ty-fst b₁'))

      p : subst GA.Ty (A.σ₁ γ a b a₁ b₁)
           (A.σ γ a b a₁ b₁ , ≡.refl) .fst
           ≡
           GA.σ (conᴿ γ) (F₀G₀A.mkTy (tyᴿ a) a₁')
           (F₀G₀A.mkTy (tyᴿ b) b₁') .fst
      p =
        subst GA.Ty (A.σ₁ γ a b a₁ b₁)
          (A.σ γ a b a₁ b₁ , ≡.refl) .fst
          ≡⟨ G₀A.Ty-fst (A.σ₁ γ a b a₁ b₁) ⟩
        A.σ γ a b a₁ b₁
          ≡⟨ ≡.dcongsspp (A.σ γ)
               (≡.sym pa)
               pb ⟩
        A.σ γ (subst GA.Ty a₁' (a , ≡.refl) .fst)
              (subst GA.Ty b₁' (b , ≡.refl) .fst)
              (subst GA.Ty a₁' (a , ≡.refl) .snd)
              (subst GA.Ty b₁' (b , ≡.refl) .snd)
          ≡⟨ ≡.refl ⟩
        GA.σ γ (subst GA.Ty a₁' (a , ≡.refl))
               (subst GA.Ty b₁' (b , ≡.refl)) .fst
          ≡⟨ ≡.refl ⟩
        GA.σ γ (F₀G₀A.mkTy (A.ty₁ a , a , ≡.refl) a₁')
           (F₀G₀A.mkTy (tyᴿ b) b₁') .fst
          ≡⟨ ≡.refl ⟩
        GA.σ (conᴿ γ) (F₀G₀A.mkTy (tyᴿ a) a₁')
           (F₀G₀A.mkTy (tyᴿ b) b₁') .fst ∎

  ε₀ : (A : M.Algebra ℓA) → M.Cat ℓA [ F₀ (G₀ A) , A ]
  ε₀ A = record
    { conᴿ = conᴿ
    ; tyᴿ = tyᴿ
    ; ty₁ᴿ = ty₁ᴿ
    ; ∙ᴿ = ∙ᴿ
    ; ▷ᴿ = ▷ᴿ
    ; uᴿ = uᴿ
    ; πᴿ = πᴿ
    ; σᴿ = σᴿ
    }
    module ε₀ where
    open ≡
    open ≡-Reasoning
    module A = M.Algebra A
    module GA = D.Algebra (G₀ A)
    module G₀A = G₀ A
    module FGA = M.Algebra (F₀ (G₀ A))
    module F₀G₀A = F₀ (G₀ A)

    conᴿ : FGA.Con → A.Con
    conᴿ γ = γ

    tyᴿ : FGA.Ty → A.Ty
    tyᴿ (γ , (a , a₁)) = a

    ty₁ᴿ : ∀ a → A.ty₁ (tyᴿ a) ≡ conᴿ (FGA.ty₁ a)
    ty₁ᴿ (γ , (a , a₁)) = a₁

    ∙ᴿ : conᴿ FGA.∙ ≡ A.∙
    ∙ᴿ = ≡.refl

    ▷ᴿ : ∀ γ a
      → (a₁ : FGA.ty₁ a ≡ γ)
      → (a₁' : A.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → conᴿ (FGA.▷ γ a a₁) ≡ A.▷ (conᴿ γ) (tyᴿ a) a₁'
    ▷ᴿ γ (γ , a , refl) refl refl = refl

    uᴿ : ∀ γ → tyᴿ (FGA.u γ) ≡ A.u (conᴿ γ)
    uᴿ γ = refl

    πᴿ : ∀ γ a b
      → (a₁ : FGA.ty₁ a ≡ γ)
      → (b₁ : FGA.ty₁ b ≡ FGA.▷ γ a a₁)
      → (a₁' : A.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → (b₁' : A.ty₁ (tyᴿ b) ≡ A.▷ (conᴿ γ) (tyᴿ a) a₁')
      → tyᴿ (FGA.π γ a b a₁ b₁)
      ≡ A.π (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
    πᴿ γ (γ , a , refl) (δ , b , refl) refl b₁ refl b₁' =
      tyᴿ
       (FGA.π (A.ty₁ a)
        (A.ty₁ a , a , refl) (A.ty₁ b , b , refl) refl b₁)
        ≡⟨ refl ⟩
      A.π (A.ty₁ a) (F₀G₀A.mkTy (A.ty₁ a , a , refl) refl .fst) 
        (F₀G₀A.mkTy (A.ty₁ b , b , refl) b₁ .fst)
        (F₀G₀A.mkTy (A.ty₁ a , a , refl) refl .snd)
        (F₀G₀A.mkTy (A.ty₁ b , b , refl) b₁ .snd)
        ≡⟨ dcongsspp (A.π (A.ty₁ a)) refl (G₀.Ty-fst A b₁) ⟩
      A.π (A.ty₁ a) a b refl b₁' ∎

    σᴿ : ∀ γ a b
      → (a₁ : FGA.ty₁ a ≡ γ)
      → (b₁ : FGA.ty₁ b ≡ FGA.▷ γ a a₁)
      → (a₁' : A.ty₁ (tyᴿ a) ≡ conᴿ γ)
      → (b₁' : A.ty₁ (tyᴿ b) ≡ A.▷ (conᴿ γ) (tyᴿ a) a₁')
      → tyᴿ (FGA.σ γ a b a₁ b₁)
      ≡ A.σ (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
    σᴿ γ (γ , a , refl) (δ , b , refl) refl b₁ refl b₁' =
      tyᴿ
       (FGA.σ (A.ty₁ a)
        (A.ty₁ a , a , refl) (A.ty₁ b , b , refl) refl b₁)
        ≡⟨ refl ⟩
      A.σ (A.ty₁ a) (F₀G₀A.mkTy (A.ty₁ a , a , refl) refl .fst) 
        (F₀G₀A.mkTy (A.ty₁ b , b , refl) b₁ .fst)
        (F₀G₀A.mkTy (A.ty₁ a , a , refl) refl .snd)
        (F₀G₀A.mkTy (A.ty₁ b , b , refl) b₁ .snd)
        ≡⟨ dcongsspp (A.σ (A.ty₁ a)) refl (G₀.Ty-fst A b₁) ⟩
      A.σ (A.ty₁ a) a b refl b₁' ∎

  ε₁ : {A B : M.Algebra ℓA} (f : M.Hom A B)
    → f M.∘ ε₀ A
    M.≈ ε₀ B M.∘ F₁ (G₁ {A = A} {B} f)
  ε₁ {A} {B} f = M.mk≈ (λ γ → ≡.refl) (λ a → ≡.refl)

  isIso-ε : ∀ A → IsIso (M.Cat ℓA) (ε₀ A)
  isIso-ε A = record
    { f⁻¹ = ε⁻₀ A
    ; linv = M.mk≈ (λ γ → ≡.refl) p
    ; rinv = M.mk≈ (λ γ → ≡.refl) (λ a → ≡.refl)
    }
    where
    module isIso-ε where
    open ≡
    open ≡-Reasoning
    module A = M.Algebra A
    module GA = D.Algebra (G₀ A)
    module G₀A = G₀ A
    module FGA = M.Algebra (F₀ (G₀ A))
    module F₀GA = F₀ (G₀ A)
    module ε⁻A = M.Hom (ε⁻₀ A)
    module εA = M.Hom (ε₀ A)
    module ε⁻εA = M.Hom (ε⁻₀ A M.∘ ε₀ A)
    p : (a : FGA.Ty)
      → ε⁻εA.tyᴿ a ≡ a
    p (γ , a , a₁) =
      Σ≡ a₁ (ΣP≡ _ _ (G₀A.Ty-fst a₁))

equiv : Equivalence (D.Cat ℓA) (M.Cat ℓA)
equiv {ℓA} = record
  { F = F
  ; G = G
  ; η = η
  ; ε = ε }
