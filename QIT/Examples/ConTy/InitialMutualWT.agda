open import QIT.Prelude
open import QIT.Prop
open import QIT.Examples.ConTy.MutualWeaklyTagged as W
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Setoid

module QIT.Examples.ConTy.InitialMutualWT {ℓI}
  ⦃ pathElim* : PathElim ⦄
  (I : Algebra ℓI)
  (rec : ∀ {ℓA} (A : Algebra ℓA) → Hom I A)
  (recUnique : ∀ {ℓA} {A : Algebra ℓA} → (f : Hom I A) → f ≈ rec A)
  where

module I = Algebra I
module rec {ℓA} A = Hom (rec {ℓA} A)

record DispAlgebra ℓX : Set (lsuc (ℓI ⊔ ℓX)) where
  no-eta-equality
  field
    CT : I.CT → Set ℓX
    [] : ∀ x → CT x → CT (I.[ x ])
    k̂ : CT I.k̂
    ĉ : CT I.ĉ
    t̂ : CT I.t̂
    kk̂ : subst CT I.kk̂ ([] I.k̂ k̂) ≡ k̂
    kĉ : subst CT I.kĉ ([] I.ĉ ĉ) ≡ k̂
    kt̂ : subst CT I.kt̂ ([] I.t̂ t̂) ≡ k̂
    ty₁ : ∀ a → CT a → CT (I.ty₁ a)
    kty₁ : ∀ a (aᴰ : CT a)
      → (ka : I.[ a ] ≡ I.t̂)
      → subst CT (I.kty₁ a ka) ([] (I.ty₁ a) (ty₁ a aᴰ)) ≡ ĉ
    kty₁-a : ∀ a (aᴰ : CT a)
      → (ka : I.[ I.ty₁ a ] ≡ I.ĉ)
      → subst CT (I.kty₁-a a ka) ([] a aᴰ) ≡ t̂

    ∙ : CT I.∙
    k∙ : subst CT I.k∙ ([] I.∙ ∙) ≡ ĉ
    ▷ : ∀ γ a → CT γ → CT a → CT (I.▷ γ a)
    k▷ : ∀ γ a (γᴰ : CT γ) (aᴰ : CT a)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂)
      → (a₁ : I.ty₁ a ≡ γ)
      → subst CT (I.k▷ γ a kγ ka a₁)
          ([] (I.▷ γ a) (▷ γ a γᴰ aᴰ)) ≡ ĉ
    ▷-γ : ∀ γ a (γᴰ : CT γ)
      → (k▷ : I.[ I.▷ γ a ] ≡ I.ĉ)
      → subst CT (I.▷-γ γ a k▷) ([] γ γᴰ) ≡ ĉ
    ▷-a : ∀ γ a (aᴰ : CT a)
      → (k▷ : I.[ I.▷ γ a ] ≡ I.ĉ)
      → subst CT (I.▷-a γ a k▷) ([] a aᴰ) ≡ t̂
    ▷-a₁ : ∀ γ a (γᴰ : CT γ) (aᴰ : CT a)
      → (k▷ : I.[ I.▷ γ a ] ≡ I.ĉ)
      → subst CT (I.▷-a₁ γ a k▷) (ty₁ a aᴰ) ≡ γᴰ

    u : ∀ γ → CT γ → CT (I.u γ)
    ku : ∀ γ (γᴰ : CT γ)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → subst CT (I.ku γ kγ) ([] (I.u γ) (u γ γᴰ)) ≡ t̂
    u₁ : ∀ γ (γᴰ : CT γ)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → subst CT (I.u₁ γ kγ) (ty₁ (I.u γ) (u γ γᴰ)) ≡ γᴰ
    u-γ : ∀ γ (γᴰ : CT γ)
      → (ku : I.[ I.u γ ] ≡ I.t̂)
      → subst CT (I.u-γ γ ku) ([] γ γᴰ) ≡ ĉ

    π : ∀ γ a b → CT γ → CT a → CT b → CT (I.π γ a b)
    kπ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂)
      → (a₁ : I.ty₁ a ≡ γ)
      → (kb : I.[ b ] ≡ I.t̂)
      → (b₁ : I.ty₁ b ≡ I.▷ γ a)
      → subst CT (I.kπ γ a b kγ ka a₁ kb b₁)
          ([] (I.π γ a b) (π γ a b γᴰ aᴰ bᴰ)) ≡ t̂
    π₁ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kπ : I.[ I.π γ a b ] ≡ I.t̂)
      → subst CT (I.π₁ γ a b kπ)
          (ty₁ (I.π γ a b) (π γ a b γᴰ aᴰ bᴰ)) ≡ γᴰ
    π-γ : ∀ γ a b (γᴰ : CT γ)
      → (kπ : I.[ I.π γ a b ] ≡ I.t̂)
      → subst CT (I.π-γ γ a b kπ) ([] γ γᴰ) ≡ ĉ
    π-a : ∀ γ a b (aᴰ : CT a)
      → (kπ : I.[ I.π γ a b ] ≡ I.t̂)
      → subst CT (I.π-a γ a b kπ) ([] a aᴰ) ≡ t̂
    π-a₁ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a)
      → (kπ : I.[ I.π γ a b ] ≡ I.t̂)
      → subst CT (I.π-a₁ γ a b kπ) (ty₁ a aᴰ) ≡ γᴰ
    π-b : ∀ γ a b (bᴰ : CT b)
      → (kπ : I.[ I.π γ a b ] ≡ I.t̂)
      → subst CT (I.π-b γ a b kπ) ([] b bᴰ) ≡ t̂
    π-b₁ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kπ : I.[ I.π γ a b ] ≡ I.t̂)
      → subst CT (I.π-b₁ γ a b kπ) (ty₁ b bᴰ)
      ≡ ▷ γ a γᴰ aᴰ

    σ : ∀ γ a b → CT γ → CT a → CT b → CT (I.σ γ a b)
    kσ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂)
      → (a₁ : I.ty₁ a ≡ γ)
      → (kb : I.[ b ] ≡ I.t̂)
      → (b₁ : I.ty₁ b ≡ I.▷ γ a)
      → subst CT (I.kσ γ a b kγ ka a₁ kb b₁)
          ([] (I.σ γ a b) (σ γ a b γᴰ aᴰ bᴰ)) ≡ t̂
    σ₁ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kσ : I.[ I.σ γ a b ] ≡ I.t̂)
      → subst CT (I.σ₁ γ a b kσ)
          (ty₁ (I.σ γ a b) (σ γ a b γᴰ aᴰ bᴰ)) ≡ γᴰ
    σ-γ : ∀ γ a b (γᴰ : CT γ)
      → (kσ : I.[ I.σ γ a b ] ≡ I.t̂)
      → subst CT (I.σ-γ γ a b kσ) ([] γ γᴰ) ≡ ĉ
    σ-a : ∀ γ a b (aᴰ : CT a)
      → (kσ : I.[ I.σ γ a b ] ≡ I.t̂)
      → subst CT (I.σ-a γ a b kσ) ([] a aᴰ) ≡ t̂
    σ-a₁ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a)
      → (kσ : I.[ I.σ γ a b ] ≡ I.t̂)
      → subst CT (I.σ-a₁ γ a b kσ) (ty₁ a aᴰ) ≡ γᴰ
    σ-b : ∀ γ a b (bᴰ : CT b)
      → (kσ : I.[ I.σ γ a b ] ≡ I.t̂)
      → subst CT (I.σ-b γ a b kσ) ([] b bᴰ) ≡ t̂
    σ-b₁ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kσ : I.[ I.σ γ a b ] ≡ I.t̂)
      → subst CT (I.σ-b₁ γ a b kσ) (ty₁ b bᴰ)
      ≡ ▷ γ a γᴰ aᴰ
    σ▷ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂)
      → (a₁ : I.ty₁ a ≡ γ)
      → (kb : I.[ b ] ≡ I.t̂)
      → (b₁ : I.ty₁ b ≡ I.▷ γ a)
      → subst CT (I.σ▷ γ a b kγ ka a₁ kb b₁)
          (▷ (I.▷ γ a) b (▷ γ a γᴰ aᴰ) bᴰ)
      ≡ ▷ γ (I.σ γ a b) γᴰ (σ γ a b γᴰ aᴰ bᴰ)
    σπ : ∀ γ a b c
      (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b) (cᴰ : CT c)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂)
      → (a₁ : I.ty₁ a ≡ γ)
      → (kb : I.[ b ] ≡ I.t̂)
      → (b₁ : I.ty₁ b ≡ I.▷ γ a)
      → (kc : I.[ c ] ≡ I.t̂)
      → (c₁ : I.ty₁ c ≡ I.▷ (I.▷ γ a) b)
      → subst CT (I.σπ γ a b c kγ ka a₁ kb b₁ kc c₁)
          (π γ a (I.π (I.▷ γ a) b c)
             γᴰ aᴰ (π (I.▷ γ a) b c (▷ γ a γᴰ aᴰ) bᴰ cᴰ))
      ≡ π γ (I.σ γ a b) c γᴰ (σ γ a b γᴰ aᴰ bᴰ) cᴰ

ΣAlg : ∀ {ℓX} → DispAlgebra ℓX → Algebra (ℓI ⊔ ℓX)
ΣAlg D = record
  { CT = Σ I.CT D.CT
  ; [_] = λ (x , xᴰ) → I.[ x ] , D.[] x xᴰ
  ; k̂ = I.k̂ , D.k̂
  ; ĉ = I.ĉ , D.ĉ
  ; t̂ = I.t̂ , D.t̂
  ; kk̂ = Σ≡ I.kk̂ D.kk̂
  ; kĉ = Σ≡ I.kĉ D.kĉ
  ; kt̂ = Σ≡ I.kt̂ D.kt̂
  ; ty₁ = λ (a , aᴰ) → I.ty₁ a , D.ty₁ a aᴰ
  ; kty₁ = λ (a , aᴰ) ka →
      Σ≡ (I.kty₁ a (cb ka)) (D.kty₁ a aᴰ (cb ka))
  ; kty₁-a = λ (a , aᴰ) ka →
      Σ≡ (I.kty₁-a a (cb ka)) (D.kty₁-a a aᴰ (cb ka))
  ; ∙ = I.∙ , D.∙
  ; k∙ = Σ≡ I.k∙ D.k∙
  ; ▷ = λ (γ , γᴰ) (a , aᴰ) → I.▷ γ a , D.▷ γ a γᴰ aᴰ
  ; k▷ = λ (γ , γᴰ) (a , aᴰ) kγ ka a₁ →
      Σ≡ (I.k▷ γ a (cb kγ) (cb ka) (cb a₁))
        (D.k▷ γ a γᴰ aᴰ (cb kγ) (cb ka) (cb a₁))
  ; ▷-γ = λ (γ , γᴰ) (a , aᴰ) k▷ →
      Σ≡ (I.▷-γ γ a (cb k▷)) (D.▷-γ γ a γᴰ (cb k▷))
  ; ▷-a = λ (γ , γᴰ) (a , aᴰ) k▷ →
      Σ≡ (I.▷-a γ a (cb k▷)) (D.▷-a γ a aᴰ (cb k▷))
  ; ▷-a₁ = λ (γ , γᴰ) (a , aᴰ) k▷ →
      Σ≡ (I.▷-a₁ γ a (cb k▷)) (D.▷-a₁ γ a γᴰ aᴰ (cb k▷))
  ; u = λ (γ , γᴰ) → I.u γ , D.u γ γᴰ
  ; ku = λ (γ , γᴰ) kγ →
      Σ≡ (I.ku γ (cb kγ)) (D.ku γ γᴰ (cb kγ))
  ; u₁ = λ (γ , γᴰ) kγ →
      Σ≡ (I.u₁ γ (cb kγ)) (D.u₁ γ γᴰ (cb kγ))
  ; u-γ = λ (γ , γᴰ) ku →
      Σ≡ (I.u-γ γ (cb ku)) (D.u-γ γ γᴰ (cb ku))
  ; π = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) →
      I.π γ a b , D.π γ a b γᴰ aᴰ bᴰ
  ; kπ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kγ ka a₁ kb b₁ →
      Σ≡ (I.kπ γ a b (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁))
        (D.kπ γ a b γᴰ aᴰ bᴰ
          (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁))
  ; π₁ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kπ →
      Σ≡ (I.π₁ γ a b (cb kπ)) (D.π₁ γ a b γᴰ aᴰ bᴰ (cb kπ))
  ; π-γ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kπ →
      Σ≡ (I.π-γ γ a b (cb kπ)) (D.π-γ γ a b γᴰ (cb kπ))
  ; π-a = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kπ →
      Σ≡ (I.π-a γ a b (cb kπ)) (D.π-a γ a b aᴰ (cb kπ))
  ; π-a₁ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kπ →
      Σ≡ (I.π-a₁ γ a b (cb kπ)) (D.π-a₁ γ a b γᴰ aᴰ (cb kπ))
  ; π-b = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kπ →
      Σ≡ (I.π-b γ a b (cb kπ)) (D.π-b γ a b bᴰ (cb kπ))
  ; π-b₁ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kπ →
      Σ≡ (I.π-b₁ γ a b (cb kπ))
        (D.π-b₁ γ a b γᴰ aᴰ bᴰ (cb kπ))
  ; σ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) →
      I.σ γ a b , D.σ γ a b γᴰ aᴰ bᴰ
  ; kσ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kγ ka a₁ kb b₁ →
      Σ≡ (I.kσ γ a b (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁))
        (D.kσ γ a b γᴰ aᴰ bᴰ
          (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁))
  ; σ₁ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kσ →
      Σ≡ (I.σ₁ γ a b (cb kσ)) (D.σ₁ γ a b γᴰ aᴰ bᴰ (cb kσ))
  ; σ-γ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kσ →
      Σ≡ (I.σ-γ γ a b (cb kσ)) (D.σ-γ γ a b γᴰ (cb kσ))
  ; σ-a = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kσ →
      Σ≡ (I.σ-a γ a b (cb kσ)) (D.σ-a γ a b aᴰ (cb kσ))
  ; σ-a₁ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kσ →
      Σ≡ (I.σ-a₁ γ a b (cb kσ)) (D.σ-a₁ γ a b γᴰ aᴰ (cb kσ))
  ; σ-b = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kσ →
      Σ≡ (I.σ-b γ a b (cb kσ)) (D.σ-b γ a b bᴰ (cb kσ))
  ; σ-b₁ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kσ →
      Σ≡ (I.σ-b₁ γ a b (cb kσ))
        (D.σ-b₁ γ a b γᴰ aᴰ bᴰ (cb kσ))
  ; σ▷ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kγ ka a₁ kb b₁ →
      Σ≡ (I.σ▷ γ a b (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁))
        (D.σ▷ γ a b γᴰ aᴰ bᴰ
          (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁))
  ; σπ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) (c , cᴰ)
      kγ ka a₁ kb b₁ kc c₁ →
      Σ≡ (I.σπ γ a b c
            (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁) (cb kc) (cb c₁))
        (D.σπ γ a b c γᴰ aᴰ bᴰ cᴰ
          (cb kγ) (cb ka) (cb a₁) (cb kb) (cb b₁) (cb kc) (cb c₁))
  }
  where
  module D = DispAlgebra D
  base : Σ I.CT D.CT → I.CT
  base (x , xᴰ) = x
  cb : ∀ {x y : Σ I.CT D.CT} → x ≡ y → base x ≡ base y
  cb = ≡.cong base

projHom : ∀ {ℓX} (D : DispAlgebra ℓX) → Hom (ΣAlg D) I
projHom D = record
  { θ = λ (x , xᴰ) → x
  ; [_] = λ _ → ≡.refl
  ; k̂ = ≡.refl
  ; ĉ = ≡.refl
  ; t̂ = ≡.refl
  ; ty₁ = λ _ → ≡.refl
  ; ∙ = ≡.refl
  ; ▷ = λ _ _ _ _ _ → ≡.refl
  ; u = λ _ _ → ≡.refl
  ; π = λ _ _ _ _ _ _ _ _ → ≡.refl
  ; σ = λ _ _ _ _ _ _ _ _ → ≡.refl
  }

elimHom₀ : ∀ {ℓX} (D : DispAlgebra ℓX) → Hom I (ΣAlg D)
elimHom₀ D = rec (ΣAlg D)

proj∘elim≈id : ∀ {ℓX} (D : DispAlgebra ℓX)
  → (projHom D ∘ elimHom₀ D) ≈ id
proj∘elim≈id D =
  trans (recUnique (projHom D ∘ elimHom₀ D)) (sym (recUnique id))
  where open Setoid (HomSetoid I I)

record DisplayedHom {ℓX} (D : DispAlgebra ℓX) : Set (lsuc (ℓI ⊔ ℓX)) where
  no-eta-equality
  field
    hom : Hom I (ΣAlg D)
    beta : (projHom D ∘ elimHom₀ D) ≈ id
  open Hom hom public
  open _≈_ beta
  fst≡ : ∀ x → proj₁ (rec.θ (ΣAlg D) x) ≡ x
  fst≡ = θ≡

elimHom : ∀ {ℓX} (D : DispAlgebra ℓX) → DisplayedHom D
elimHom D = record
  { hom = elimHom₀ D
  ; beta = proj∘elim≈id D
  }

run : ∀ {ℓX} (X : Set ℓX) → AlgebraWithMotive X → I.CT → X
run X A x = subst (λ Y → Y) A.motive (rec.θ A.DA x)
  where
  module A = AlgebraWithMotive A

rec₂ : ∀ {ℓM}
  → (M : Set (ℓM ⊔ ℓA))
  → (A : AlgebraWithMotive (AlgebraWithMotive M))
  → I.CT → I.CT → M
rec₂ {ℓM} M A x y = m₂
  where
  M' : Set _
  M' = AlgebraWithMotive M
  m₁ : M'
  m₁ = run M' A x
  m₂ : M
  m₂ = run M m₁ y

record DispAlgebraWithMotive {ℓX} (M : I.CT → Set ℓX) : Set (lsuc ℓI ⊔ lsuc ℓX) where
  field
    DA : DispAlgebra ℓX
  open DispAlgebra DA public
  field
    motive : CT ≡ M

runD : ∀ {ℓM} (M : I.CT → Set ℓM) → DispAlgebraWithMotive M
  → (x : I.CT) → M x
runD M DA x = subst (λ F → F x) DA.motive y
  where
  module DA = DispAlgebraWithMotive DA
  module DD = DispAlgebra DA.DA
  module EH = DisplayedHom (elimHom DA.DA)
  fstΣ : Σ I.CT DD.CT → I.CT
  fstΣ (x , xᴰ) = x
  sndΣ : (z : Σ I.CT DD.CT) → DD.CT (fstΣ z)
  sndΣ (x , xᴰ) = xᴰ
  pair : Σ I.CT DD.CT
  pair = EH.θ x
  y : DD.CT x
  y = subst DD.CT (EH.fst≡ x) (sndΣ pair)

elim₂ : ∀ {ℓM}
  → (M : I.CT → I.CT → Set (ℓM ⊔ ℓA))
  → (A : DispAlgebraWithMotive
      (λ x → DispAlgebraWithMotive (λ y → M x y)))
  → ∀ x y → M x y
elim₂ {ℓM} M A x y = m₂
  where
  M' : (x : I.CT) → Set _
  M' x = DispAlgebraWithMotive (λ y → M x y)
  m₁ : M' x
  m₁ = runD M' A x
  m₂ : M x y
  m₂ = runD (M x) m₁ y

{-
module Code where
  open Algebra renaming ([_] to [])
  A : Algebra (lsuc (lsuc ℓI))
  A .CT = Algebra (lsuc ℓI)
  A .[] x .CT = Prop ℓI
  A .[] x .[] y = {!!}
  A .[] x .k̂ = {!!}
  A .[] x .ĉ = {!!}
  A .[] x .t̂ = {!!}
  A .[] x .ty₁ = {!!}
  A .[] x .kty₁ = {!!}
  A .[] x .kk̂ = {!!}
  A .[] x .kĉ = {!!}
  A .[] x .kt̂ = {!!}
  A .[] x .∙ = {!!}
  A .[] x .k∙ = {!!}
  A .[] x .▷ = {!!}
  A .[] x .k▷ = {!!}
  A .[] x .▷-γ = {!!}
  A .[] x .▷-a = {!!}
  A .[] x .▷-a₁ = {!!}
  A .[] x .u = {!!}
  A .[] x .ku = {!!}
  A .[] x .u₁ = {!!}
  A .[] x .u-γ = {!!}
  A .[] x .π = {!!}
  A .[] x .kπ = {!!}
  A .[] x .π₁ = {!!}
  A .[] x .π-γ = {!!}
  A .[] x .π-a = {!!}
  A .[] x .π-a₁ = {!!}
  A .[] x .π-b = {!!}
  A .[] x .π-b₁ = {!!}
  A .[] x .σ = {!!}
  A .[] x .kσ = {!!}
  A .[] x .σ₁ = {!!}
  A .[] x .σ-γ = {!!}
  A .[] x .σ-a = {!!}
  A .[] x .σ-a₁ = {!!}
  A .[] x .σ-b = {!!}
  A .[] x .σ-b₁ = {!!}
  A .[] x .σ▷ = {!!}
  A .[] x .σπ = {!!}
  A .k̂ = {!!}
  A .ĉ = {!!}
  A .t̂ = {!!}
  A .ty₁ = {!!}
  A .kty₁ = {!!}
  A .kk̂ = {!!}
  A .kĉ = {!!}
  A .kt̂ = {!!}
  A .∙ = {!!}
  A .k∙ = {!!}
  A .▷ = {!!}
  A .k▷ = {!!}
  A .▷-γ = {!!}
  A .▷-a = {!!}
  A .▷-a₁ = {!!}
  A .u = {!!}
  A .ku = {!!}
  A .u₁ = {!!}
  A .u-γ = {!!}
  A .π = {!!}
  A .kπ = {!!}
  A .π₁ = {!!}
  A .π-γ = {!!}
  A .π-a = {!!}
  A .π-a₁ = {!!}
  A .π-b = {!!}
  A .π-b₁ = {!!}
  A .σ = {!!}
  A .kσ = {!!}
  A .σ₁ = {!!}
  A .σ-γ = {!!}
  A .σ-a = {!!}
  A .σ-a₁ = {!!}
  A .σ-b = {!!}
  A .σ-b₁ = {!!}
  A .σ▷ = {!!}
  A .σπ = {!!}
  ρ = rec₂ {!!} {!!} {!!}

module Code2 where
  M : I.CT → Set ℓI
  M x = PropLift ?
  open DispAlgebraWithMotive
  open DispAlgebra
  A : DispAlgebra ℓI
  A .CT = M
  A .[] x m pk pc = {!!}
  A .k̂ = {!!}
  A .ĉ = {!!}
  A .t̂ = {!!}
  A .kk̂ = {!!}
  A .kĉ = {!!}
  A .kt̂ = {!!}
  A .ty₁ = {!!}
  A .kty₁ = {!!}
  A .∙ = {!!}
  A .k∙ = {!!}
  A .▷ = {!!}
  A .k▷ = {!!}
  A .▷-γ = {!!}
  A .▷-a = {!!}
  A .▷-a₁ = {!!}
  A .u = {!!}
  A .ku = {!!}
  A .u₁ = {!!}
  A .u-γ = {!!}
  A .π = {!!}
  A .kπ = {!!}
  A .π₁ = {!!}
  A .π-γ = {!!}
  A .π-a = {!!}
  A .π-a₁ = {!!}
  A .π-b = {!!}
  A .π-b₁ = {!!}
  A .σ = {!!}
  A .kσ = {!!}
  A .σ₁ = {!!}
  A .σ-γ = {!!}
  A .σ-a = {!!}
  A .σ-a₁ = {!!}
  A .σ-b = {!!}
  A .σ-b₁ = {!!}
  A .σ▷ = {!!}
  A .σπ = {!!}
{-
  v = elim₂ M A {!!} {!!}
-}

k≢c : I.k̂ ≢ I.ĉ
k≢c p = {!!}
  where
  M : I.CT → Set ℓI
  M x = x ≡ I.k̂ → x ≡ I.ĉ → ⊥ˢ
  open DispAlgebraWithMotive
  open DispAlgebra
  A : DispAlgebra ℓI
  A .CT = M
  A .[] x m pk pc = {!!}
  A .k̂ = {!!}
  A .ĉ = {!!}
  A .t̂ = {!!}
  A .kk̂ = {!!}
  A .kĉ = {!!}
  A .kt̂ = {!!}
  A .ty₁ = {!!}
  A .kty₁ = {!!}
  A .∙ = {!!}
  A .k∙ = {!!}
  A .▷ = {!!}
  A .k▷ = {!!}
  A .▷-γ = {!!}
  A .▷-a = {!!}
  A .▷-a₁ = {!!}
  A .u = {!!}
  A .ku = {!!}
  A .u₁ = {!!}
  A .u-γ = {!!}
  A .π = {!!}
  A .kπ = {!!}
  A .π₁ = {!!}
  A .π-γ = {!!}
  A .π-a = {!!}
  A .π-a₁ = {!!}
  A .π-b = {!!}
  A .π-b₁ = {!!}
  A .σ = {!!}
  A .kσ = {!!}
  A .σ₁ = {!!}
  A .σ-γ = {!!}
  A .σ-a = {!!}
  A .σ-a₁ = {!!}
  A .σ-b = {!!}
  A .σ-b₁ = {!!}
  A .σ▷ = {!!}
  A .σπ = {!!}
  v = elim₂ M A {!!} {!!}
-}
