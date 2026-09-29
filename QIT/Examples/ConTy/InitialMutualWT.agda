open import QIT.Prelude
open import QIT.Prop
open import QIT.Maybe
open import QIT.Examples.ConTy.MutualWeaklyTagged as W
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Setoid
import QIT.Set.Base as Set

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

data Tag : Set where
  k₀ c₀ t₀ : Tag

_≟ᵗ_ : (x y : Tag) → Decᵖ (x ≡ y)
k₀ ≟ᵗ k₀ = yes ≡.refl
k₀ ≟ᵗ c₀ = no λ ()
k₀ ≟ᵗ t₀ = no λ ()
c₀ ≟ᵗ k₀ = no λ ()
c₀ ≟ᵗ c₀ = yes ≡.refl
c₀ ≟ᵗ t₀ = no λ ()
t₀ ≟ᵗ k₀ = no λ ()
t₀ ≟ᵗ c₀ = no λ ()
t₀ ≟ᵗ t₀ = yes ≡.refl

data Class₀ : Set where
  []k̂₀ : Tag → Class₀
  []ĉ₀ []t̂₀ : Class₀

[]k̂₀-inj : ∀ {x y} → []k̂₀ x ≡ []k̂₀ y → x ≡ y
[]k̂₀-inj ≡.refl = ≡.refl

_≟ᶜ_ : (x y : Class₀) → Decᵖ (x ≡ y)
[]k̂₀ x ≟ᶜ []k̂₀ y with x ≟ᵗ y
... | yes p = yes (≡.cong []k̂₀ p)
... | no p = no (λ q → p ([]k̂₀-inj q))
[]k̂₀ _ ≟ᶜ []ĉ₀ = no λ ()
[]k̂₀ _ ≟ᶜ []t̂₀ = no λ ()
[]ĉ₀ ≟ᶜ []k̂₀ _ = no λ ()
[]ĉ₀ ≟ᶜ []ĉ₀ = yes ≡.refl
[]ĉ₀ ≟ᶜ []t̂₀ = no λ ()
[]t̂₀ ≟ᶜ []k̂₀ _ = no λ ()
[]t̂₀ ≟ᶜ []ĉ₀ = no λ ()
[]t̂₀ ≟ᶜ []t̂₀ = yes ≡.refl

pattern # = nothing

pattern []k̂ x = just ([]k̂₀ x)
pattern []ĉ = just []ĉ₀
pattern []t̂ = just []t̂₀

Class = Maybe Class₀

Tag→CT : Tag → I.CT
Tag→CT k₀ = I.k̂
Tag→CT c₀ = I.ĉ
Tag→CT t₀ = I.t̂

Class₀→Tag₀ : Class₀ → Tag
Class₀→Tag₀ ([]k̂₀ _) = k₀
Class₀→Tag₀ []ĉ₀ = c₀
Class₀→Tag₀ []t̂₀ = t₀

Class→Tag : Class → Maybe Tag
Class→Tag = map Class₀→Tag₀ 

Class₀→CT : Class₀ → I.CT
Class₀→CT g = Tag→CT (Class₀→Tag₀ g)

-- # -> nothing
-- []k̂ _ -> I.k̂
-- []ĉ -> I.ĉ
-- []t̂ -> I.t̂
Class→CT : Class → Maybe I.CT
Class→CT = map Class₀→CT

require[] : ∀ {X : Set} → Class₀ → X → (Class → Maybe X)
require[] a x b =
  b >>= λ b₀ → ifᵖ b₀ ≟ᶜ a then just x else nothing

CT→Class : I.CT → Class
CT→Class = run Class A
  module CT→Class where
  open ≡
  open Algebra renaming ([_] to [])

  DA : Algebra ℓ0
  DA .CT = Class
  DA .[] = map []k̂₀ Set.∘ map Class₀→Tag₀
  DA .k̂ = []k̂ k₀
  DA .ĉ = []k̂ c₀
  DA .t̂ = []k̂ t₀
  DA .ty₁ = require[] []t̂₀ []ĉ₀
  DA .kty₁ []t̂ refl = refl
  DA .kty₁-a []t̂ refl = refl
  DA .kk̂ = refl
  DA .kĉ = refl
  DA .kt̂ = refl
  DA .∙ = []ĉ
  DA .k∙ = refl
  DA .▷ = flatten2 (require[] []ĉ₀ (require[] []t̂₀ []ĉ₀))
  DA .k▷ []ĉ []t̂ refl refl refl = refl
  DA .▷-γ []ĉ []t̂ refl = refl
  DA .▷-a []ĉ []t̂ refl = refl
  DA .▷-a₁ []ĉ []t̂ refl = refl
  DA .u = require[] []ĉ₀ []t̂₀
  DA .ku []ĉ refl = refl
  DA .u₁ []ĉ refl = refl
  DA .u-γ []ĉ refl = refl
  DA .π = flatten3 (require[] []ĉ₀ (require[] []t̂₀ (require[] []t̂₀ []t̂₀)))
  DA .kπ []ĉ []t̂ []t̂ refl refl refl refl refl = refl
  DA .π₁ []ĉ []t̂ []t̂ refl = refl
  DA .π-γ []ĉ []t̂ []t̂ refl = refl
  DA .π-a []ĉ []t̂ []t̂ refl = refl
  DA .π-a₁ []ĉ []t̂ []t̂ refl = refl
  DA .π-b []ĉ []t̂ []t̂ refl = refl
  DA .π-b₁ []ĉ []t̂ []t̂ refl = refl
  DA .σ = flatten3 (require[] []ĉ₀ (require[] []t̂₀ (require[] []t̂₀ []t̂₀)))
  DA .kσ []ĉ []t̂ []t̂ refl refl refl refl refl = refl
  DA .σ₁ []ĉ []t̂ []t̂ refl = refl
  DA .σ-γ []ĉ []t̂ []t̂ refl = refl
  DA .σ-a []ĉ []t̂ []t̂ refl = refl
  DA .σ-a₁ []ĉ []t̂ []t̂ refl = refl
  DA .σ-b []ĉ []t̂ []t̂ refl = refl
  DA .σ-b₁ []ĉ []t̂ []t̂ refl = refl
  DA .σ▷ []ĉ []t̂ []t̂ refl refl refl refl refl = refl
  DA .σπ []ĉ []t̂ []t̂ []t̂ refl refl refl refl refl refl refl = refl

  A : AlgebraWithMotive Class
  A = record { DA = DA ; motive = refl }

{-
class[]-correct : ∀ g s
  → CT→Class.class[] g ≡ []k̂ s
  → Class→Tag g ≡ just s
class[]-correct ([]k̂ k₀) k₀ ≡.refl = ≡.refl
class[]-correct ([]k̂ c₀) k₀ ≡.refl = ≡.refl
class[]-correct ([]k̂ t₀) k₀ ≡.refl = ≡.refl
class[]-correct []ĉ c₀ ≡.refl = ≡.refl
class[]-correct []t̂ t₀ ≡.refl = ≡.refl
class[]-correct # k₀ ()
class[]-correct # c₀ ()
class[]-correct # t₀ ()

classified-valid : ∀ {g s} → Class→Tag g ≡ just s → g ≢ #
classified-valid {([]k̂ k₀)} p ()
classified-valid {([]k̂ c₀)} p ()
classified-valid {([]k̂ t₀)} p ()
classified-valid {[]ĉ} p ()
classified-valid {[]t̂} p ()
classified-valid {#} ()

classified-correct : ∀ {g s}
  → (p : Class→Tag g ≡ just s)
  → Class₀→CT g (classified-valid p) ≡ Tag→CT s
classified-correct {([]k̂ k₀)} {k₀} ≡.refl = ≡.refl
classified-correct {([]k̂ c₀)} {k₀} ≡.refl = ≡.refl
classified-correct {([]k̂ t₀)} {k₀} ≡.refl = ≡.refl
classified-correct {[]ĉ} {c₀} ≡.refl = ≡.refl
classified-correct {[]t̂} {t₀} ≡.refl = ≡.refl
classified-correct {#} ()

module CT→Class-rec = Hom (rec CT→Class.DA)

CT→Class-Tag : ∀ s → CT→Class (Tag→CT s) ≡ []k̂ s
CT→Class-Tag k₀ = CT→Class-rec.k̂
CT→Class-Tag c₀ = CT→Class-rec.ĉ
CT→Class-Tag t₀ = CT→Class-rec.t̂

CT→Tag-correct : ∀ x s
  → I.[ x ] ≡ Tag→CT s
  → Class→Tag (CT→Class x) ≡ just s
CT→Tag-correct x s kx = class[]-correct (CT→Class x) s p
  where
  open ≡
  p : CT→Class.class[] (CT→Class x) ≡ []k̂ s
  p = trans (sym (CT→Class-rec.[ x ]))
      (trans (cong CT→Class kx) (CT→Class-Tag s))

CT→Class-correct : ∀ x s (kx : I.[ x ] ≡ Tag→CT s)
  → let p = CT→Tag-correct x s kx
    in Box (Class→CT (CT→Class x) (classified-valid p) ≡ I.[ x ])
CT→Class-correct x s kx = box
  (≡.trans (classified-correct (CT→Tag-correct x s kx)) (≡.sym kx))
-}

record PropDispAlgebra ℓX : Set (lsuc (ℓI ⊔ ℓX)) where
  no-eta-equality
  field
    CT : I.CT → Prop ℓX
    [] : ∀ x → CT x → CT (I.[ x ])
    k̂ : CT I.k̂
    ĉ : CT I.ĉ
    t̂ : CT I.t̂
    ty₁ : ∀ a → CT a → CT (I.ty₁ a)

    ∙ : CT I.∙
    ▷ : ∀ γ a → CT γ → CT a → CT (I.▷ γ a)
    u : ∀ γ → CT γ → CT (I.u γ)
    π : ∀ γ a b → CT γ → CT a → CT b → CT (I.π γ a b)
    σ : ∀ γ a b → CT γ → CT a → CT b → CT (I.σ γ a b)

PropDispAlgebra→DispAlgebra : ∀ {ℓX} → PropDispAlgebra ℓX → DispAlgebra ℓX
PropDispAlgebra→DispAlgebra PA = record
  { CT = λ x → Box (CT x)
  ; [] = λ x (box xᴰ) → box ([] x xᴰ)
  ; k̂ = box k̂
  ; ĉ = box ĉ
  ; t̂ = box t̂
  ; kk̂ = refl
  ; kĉ = refl
  ; kt̂ = refl
  ; ty₁ = λ a (box aᴰ) → box (ty₁ a aᴰ)
  ; kty₁ = λ _ _ _ → isPropBox _ _
  ; kty₁-a = λ _ _ _ → isPropBox _ _
  ; ∙ = box ∙
  ; k∙ = isPropBox _ _
  ; ▷ = λ γ a (box γᴰ) (box aᴰ) → box (▷ γ a γᴰ aᴰ)
  ; k▷ = λ _ _ _ _ _ _ _ → isPropBox _ _
  ; ▷-γ = λ _ _ _ _ → isPropBox _ _
  ; ▷-a = λ _ _ _ _ → isPropBox _ _
  ; ▷-a₁ = λ _ _ _ _ _ → isPropBox _ _
  ; u = λ γ (box γᴰ) → box (u γ γᴰ)
  ; ku = λ _ _ _ → isPropBox _ _
  ; u₁ = λ _ _ _ → isPropBox _ _
  ; u-γ = λ _ _ _ → isPropBox _ _
  ; π = λ γ a b (box γᴰ) (box aᴰ) (box bᴰ) → box (π γ a b γᴰ aᴰ bᴰ)
  ; kπ = λ _ _ _ _ _ _ _ _ _ _ _ → isPropBox _ _
  ; π₁ = λ _ _ _ _ _ _ _ → isPropBox _ _
  ; π-γ = λ _ _ _ _ _ → isPropBox _ _
  ; π-a = λ _ _ _ _ _ → isPropBox _ _
  ; π-a₁ = λ _ _ _ _ _ _ → isPropBox _ _
  ; π-b = λ _ _ _ _ _ → isPropBox _ _
  ; π-b₁ = λ _ _ _ _ _ _ _ → isPropBox _ _
  ; σ = λ γ a b (box γᴰ) (box aᴰ) (box bᴰ) → box (σ γ a b γᴰ aᴰ bᴰ)
  ; kσ = λ _ _ _ _ _ _ _ _ _ _ _ → isPropBox _ _
  ; σ₁ = λ _ _ _ _ _ _ _ → isPropBox _ _
  ; σ-γ = λ _ _ _ _ _ → isPropBox _ _
  ; σ-a = λ _ _ _ _ _ → isPropBox _ _
  ; σ-a₁ = λ _ _ _ _ _ _ → isPropBox _ _
  ; σ-b = λ _ _ _ _ _ → isPropBox _ _
  ; σ-b₁ = λ _ _ _ _ _ _ _ → isPropBox _ _
  ; σ▷ = λ _ _ _ _ _ _ _ _ _ _ _ → isPropBox _ _
  ; σπ = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → isPropBox _ _
  }
  where
  open PropDispAlgebra PA
  open ≡
