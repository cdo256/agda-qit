open import QIT.Prelude
open import QIT.Prop
open import QIT.Examples.ConTy.WeaklyTagged as W
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Setoid

module QIT.Examples.ConTy.InitialWeaklyTagged {ℓI}
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
    kk̂ : subst {ℓI} {ℓX} {I.CT} CT I.kk̂ ([] I.k̂ k̂) ≡ k̂
    ĉ : CT I.ĉ
    kĉ : subst CT I.kĉ ([] I.ĉ ĉ) ≡ k̂
    t̂ : ∀ γ → CT γ → CT (I.t̂ γ)
    kt̂ : ∀ γ (γᴰ : CT γ)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → subst CT (I.kt̂ γ kγ) ([] (I.t̂ γ) (t̂ γ γᴰ)) ≡ k̂

    ∙ : CT I.∙
    k∙ : subst CT I.k∙ ([] I.∙ ∙) ≡ ĉ
    ▷ : ∀ γ a → CT γ → CT a → CT (I.▷ γ a)
    k▷ : ∀ γ a (γᴰ : CT γ) (aᴰ : CT a)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂ γ)
      → subst CT (I.k▷ γ a kγ ka)
          ([] (I.▷ γ a) (▷ γ a γᴰ aᴰ)) ≡ ĉ
    u : ∀ γ → CT γ → CT (I.u γ)
    ku : ∀ γ (γᴰ : CT γ)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → subst CT (I.ku γ kγ) ([] (I.u γ) (u γ γᴰ)) ≡ t̂ γ γᴰ
    π : ∀ γ a b → CT γ → CT a → CT b → CT (I.π γ a b)
    kπ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂ γ)
      → (kb : I.[ b ] ≡ I.t̂ (I.▷ γ a))
      → subst CT (I.kπ γ a b kγ ka kb)
          ([] (I.π γ a b) (π γ a b γᴰ aᴰ bᴰ)) ≡ t̂ γ γᴰ
    σ : ∀ γ a b → CT γ → CT a → CT b → CT (I.σ γ a b)
    kσ : ∀ γ a b (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂ γ)
      → (kb : I.[ b ] ≡ I.t̂ (I.▷ γ a))
      → subst CT (I.kσ γ a b kγ ka kb)
          ([] (I.σ γ a b) (σ γ a b γᴰ aᴰ bᴰ)) ≡ t̂ γ γᴰ
    σ▷ : ∀ γ a b
      (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂ γ)
      → (kb : I.[ b ] ≡ I.t̂ (I.▷ γ a))
      → subst CT (I.σ▷ γ a b kγ ka kb)
          (▷ (I.▷ γ a) b (▷ γ a γᴰ aᴰ) bᴰ)
      ≡ ▷ γ (I.σ γ a b) γᴰ (σ γ a b γᴰ aᴰ bᴰ)
    σπ : ∀ γ a b c
      (γᴰ : CT γ) (aᴰ : CT a) (bᴰ : CT b) (cᴰ : CT c)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂ γ)
      → (kb : I.[ b ] ≡ I.t̂ (I.▷ γ a))
      → (kc : I.[ c ] ≡ I.t̂ (I.▷ (I.▷ γ a) b))
      → subst CT (I.σπ γ a b c kγ ka kb kc)
          (π γ a (I.π (I.▷ γ a) b c)
             γᴰ aᴰ (π (I.▷ γ a) b c (▷ γ a γᴰ aᴰ) bᴰ cᴰ))
      ≡ π γ (I.σ γ a b) c γᴰ (σ γ a b γᴰ aᴰ bᴰ) cᴰ

ΣAlg : ∀ {ℓX} → DispAlgebra ℓX → Algebra (ℓI ⊔ ℓX)
ΣAlg D = record
  { CT = Σ I.CT D.CT
  ; [_] = λ (x , xᴰ) → I.[ x ] , D.[] x xᴰ
  ; k̂ = I.k̂ , D.k̂
  ; kk̂ = Σ≡ I.kk̂ D.kk̂
  ; ĉ = I.ĉ , D.ĉ
  ; kĉ = Σ≡ I.kĉ D.kĉ
  ; t̂ = λ (γ , γᴰ) → I.t̂ γ , D.t̂ γ γᴰ
  ; kt̂ = λ (γ , γᴰ) kγ
      → Σ≡ (I.kt̂ γ (cb kγ))
          (D.kt̂ γ γᴰ (cb kγ))
  ; ∙ = I.∙ , D.∙
  ; k∙ = Σ≡ I.k∙ D.k∙
  ; ▷ = λ (γ , γᴰ) (a , aᴰ) → I.▷ γ a , D.▷ γ a γᴰ aᴰ
  ; k▷ = λ (γ , γᴰ) (a , aᴰ) kγ ka
      → Σ≡ (I.k▷ γ a (cb kγ) (cb ka))
          (D.k▷ γ a γᴰ aᴰ (cb kγ) (cb ka))
  ; u = λ (γ , γᴰ) → I.u γ , D.u γ γᴰ
  ; ku = λ (γ , γᴰ) kγ
      → Σ≡ (I.ku γ (cb kγ))
          (D.ku γ γᴰ (cb kγ))
  ; π = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ)
      → I.π γ a b , D.π γ a b γᴰ aᴰ bᴰ
  ; kπ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kγ ka kb
      → Σ≡ (I.kπ γ a b
               (cb kγ) (cb ka) (cb kb))
          (D.kπ γ a b γᴰ aᴰ bᴰ
               (cb kγ) (cb ka) (cb kb))
  ; σ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ)
      → I.σ γ a b , D.σ γ a b γᴰ aᴰ bᴰ
  ; kσ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kγ ka kb
      → Σ≡ (I.kσ γ a b
               (cb kγ) (cb ka) (cb kb))
          (D.kσ γ a b γᴰ aᴰ bᴰ
               (cb kγ) (cb ka) (cb kb))
  ; σ▷ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) kγ ka kb
      → Σ≡ (I.σ▷ γ a b
               (cb kγ) (cb ka) (cb kb))
          (D.σ▷ γ a b γᴰ aᴰ bᴰ
               (cb kγ) (cb ka) (cb kb))
  ; σπ = λ (γ , γᴰ) (a , aᴰ) (b , bᴰ) (c , cᴰ) kγ ka kb kc
      → Σ≡ (I.σπ γ a b c
               (cb kγ) (cb ka)
               (cb kb) (cb kc))
          (D.σπ γ a b c γᴰ aᴰ bᴰ cᴰ
               (cb kγ) (cb ka)
               (cb kb) (cb kc))
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
  ; t̂ = λ _ → ≡.refl
  ; ∙ = ≡.refl
  ; ▷ = λ _ _ _ _ → ≡.refl
  ; u = λ _ _ → ≡.refl
  ; π = λ _ _ _ _ _ _ → ≡.refl
  ; σ = λ _ _ _ _ _ _ → ≡.refl
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
run X A = rec.θ A.toAlgebra
  where
  module A = AlgebraWithMotive A

record DispAlgebraWithMotive {ℓX} (M : I.CT → Set ℓX) : Set (lsuc ℓI ⊔ lsuc ℓX) where
  field
    DA : DispAlgebra ℓX
  open DispAlgebra DA public
  field
    motive : CT ≡ M

runD : ∀ {ℓM} (M : I.CT → Set ℓM) → DispAlgebraWithMotive M → (x : I.CT) → M x
runD {ℓM} M DA x = subst (λ F → F x) DA.motive y
  where
  module DA = DispAlgebraWithMotive DA
  D : DispAlgebra ℓM
  D = DA.DA
  module DD = DispAlgebra D
  module EH = DisplayedHom (elimHom D)
  fstΣ : Σ I.CT DD.CT → I.CT
  fstΣ (x , xᴰ) = x
  sndΣ : (z : Σ I.CT DD.CT) → DD.CT (fstΣ z)
  sndΣ (x , xᴰ) = xᴰ
  pair : Σ I.CT DD.CT
  pair = EH.θ x
  y : DD.CT x
  y = subst DD.CT (EH.fst≡ x) (sndΣ pair)

-- CodeRows : DispAlgebraWithMotive (λ x → I.CT → Prop ℓI)
-- CodeRows = record
--   { DA = record
--     { CT = λ _ → I.CT → Prop ℓI
--     ; [_] = Row[]
--     ; k̂ = {!!}
--     ; kk̂ = {!!}
--     ; ĉ = {!!}
--     ; kĉ = {!!}
--     ; t̂ = {!!}
--     ; kt̂ = {!!}
--     ; ∙ = {!!}
--     ; k∙ = {!!}
--     ; ▷ = {!!}
--     ; k▷ = {!!}
--     ; u = {!!}
--     ; ku = {!!}
--     ; π = {!!}
--     ; kπ = {!!}
--     ; σ = {!!}
--     ; kσ = {!!}
--     ; σ▷ = {!!}
--     ; σπ = {!!}
--     }
--   ; motive = ≡.refl }
--   where
--   Row[] : (I.CT → Prop ℓI) → I.CT → Prop ℓI
--   Row[] rowP = runD (λ _ → Prop ℓI) RowAlg
--     where
--     RowAlg : DispAlgebraWithMotive (λ _ → Prop ℓI)
--     RowAlg = record
--       { DA = record
--         { CT = λ _ → Prop ℓI
--         ; [_] = λ {x} P → {!!} 
--         ; k̂ = {!!}
--         ; kk̂ = {!!}
--         ; ĉ = {!!}
--         ; kĉ = {!!}
--         ; t̂ = {!!}
--         ; kt̂ = {!!}
--         ; ∙ = {!!}
--         ; k∙ = {!!}
--         ; ▷ = {!!}
--         ; k▷ = {!!}
--         ; u = {!!}
--         ; ku = {!!}
--         ; π = {!!}
--         ; kπ = {!!}
--         ; σ = {!!}
--         ; kσ = {!!}
--         ; σ▷ = {!!}
--         ; σπ = {!!}
--         }
--       ; motive = {!!} }

-- -- record InversionMotive (x : I.CT) : Set (lsuc ℓA) where
-- --   no-eta-equality
-- --   field
-- --     []-inv-kγ : ∀ γ a
-- --       → x ≡ (I.▷ γ a)
-- --       → I.[ I.▷ γ a ] ≡ I.ĉ
-- --       → I.[ γ ] ≡ I.ĉ
-- --     ▷-inv-kγ : ∀ γ a
-- --       → x ≡ (I.▷ γ a)
-- --       → I.[ I.▷ γ a ] ≡ I.ĉ
-- --       → I.[ γ ] ≡ I.ĉ
-- --     ▷-inv-ka : ∀ γ a
-- --       → x ≡ (I.▷ γ a)
-- --       → I.[ I.▷ γ a ] ≡ I.ĉ
-- --       → I.[ a ] ≡ I.t̂ γ
-- --     u-inv-kγ : ∀ {γ γ'}
-- --       → x ≡ I.u γ
-- --       → I.[ I.u γ ] ≡ I.t̂ γ'
-- --       → I.[ γ ] ≡ I.ĉ
-- --     u-inv-γγ' : ∀ {γ γ'}
-- --       → x ≡ I.u γ
-- --       → I.[ I.u γ ] ≡ I.t̂ γ'
-- --       → γ ≡ γ'

-- -- InversionAlgebra : DispAlgebra (lsuc ℓA)
-- -- InversionAlgebra = record
-- --   { CT = InversionMotive
-- --   ; [_] = {!!}
-- --   ; k̂ = {!!}
-- --   ; kk̂ = {!!}
-- --   ; ĉ = {!!}
-- --   ; kĉ = {!!}
-- --   ; t̂ = {!!}
-- --   ; kt̂ = {!!}
-- --   ; ∙ = {!!}
-- --   ; k∙ = {!!}
-- --   ; ▷ = {!!}
-- --   ; k▷ = {!!}
-- --   ; u = {!!}
-- --   ; ku = {!!}
-- --   ; π = {!!}
-- --   ; kπ = {!!}
-- --   ; σ = {!!}
-- --   ; kσ = {!!}
-- --   ; σ▷ = {!!}
-- --   ; σπ = {!!}
-- --   }
-- --   where
-- --   [_]ᴰ : ∀ {x : I.CT} → InversionMotive x → InversionMotive I.[ x ]
-- --   [_]ᴰ {x} xᴹ = record
-- --     { ▷-inv-kγ = λ { γ a k▷ x≡ → {!!} }
-- --     ; ▷-inv-ka = {!!}
-- --     ; u-inv-kγ = {!!}
-- --     ; u-inv-γγ' = {!!} }
-- --     where
-- --     module xᴹ = InversionMotive xᴹ
