module QIT.Category.WithFamilies where
-- Category With Families (as model of dependent type theory)
-- see https://ncatlab.org/nlab/show/categorical+model+of+dependent+types#categories_with_families
-- for more details.
-- Initially derived from https://github.com/agda/agda-categories/blob/14e7fa985f115c77f154a04ecfd4973560293505/src/Categories/Category/WithFamilies.agda
-- Note that this was removed in the most recent version.
-- Since reformulated to follow Castellan-Clairambault-Dybjer's 2021 paper:
-- "Categories with Families: Unityped, Simply Typed, and Dependently Typed"

open import QIT.Prelude hiding (_,_)
open import QIT.Prop hiding (_,_)
open import QIT.Setoid
open import QIT.Category.Base
open import QIT.Functor.Base
open import QIT.NatTrans
open import QIT.Category.FamilyOfSets
open import QIT.Category.Terminal

-- open import Categories.Category.Instance.FamilyOfSets
-- open import Categories.Functor.Presheaf
-- open import Categories.Category.Slice
open import QIT.Category.Set

private
  variable
    ℓCo ℓCh ℓCe : Level
    ℓA ℓB : Level

record CategoryWithFamilies : Set₁ where
  field
    -- C : Category ℓCo ℓCh ℓCe
    C : Category ℓ0 ℓ0 ℓ0
  open Category C renaming (Obj to Ctx)
  field
    ∙ : Ctx
    ⟨⟩_ : (Γ : Ctx) → Γ ⇒ ∙
    ⟨⟩-unique : (Γ : Ctx) → isProp (Γ ⇒ ∙)
    T : Functor (C op) (FamilyOfSets ℓ0 ℓ0)

  module T = Functor T
  open Fam renaming (T to S)
  open FamCat

  Ty : Ctx → Set
  Ty Γ = T.ob Γ .U
  Tm : ∀ Γ → (Ty Γ) → Set
  Tm Γ A = T.ob Γ .S A
  _[_]t : ∀ {Γ Δ} → Ty Δ → (σ : Γ ⇒ Δ) → Ty Γ
  _[_]t A σ = Hom.map (T.hom σ) A
  _[_]m : ∀ {Γ Δ} → {A : Ty Δ} (t : Tm Δ A) (σ : Γ ⇒ Δ) → Tm Γ (A [ σ ]t)
  _[_]m {A = A} t σ = Hom.transport (T.hom σ) t

  field
    _▷_ : (Γ : Ctx) → Ty Γ → Ctx
    π₁ : ∀ {Γ} (A : Ty Γ) → (Γ ▷ A) ⇒ Γ
    π₂ : ∀ {Γ} (A : Ty Γ) → Tm (Γ ▷ A) (A [ π₁ A ]t)
    _,_ : ∀ {Γ Δ} {A : Ty Δ} (σ : Γ ⇒ Δ)
          → (a : Tm Γ (A [ σ ]t))
          → Γ ⇒ (Δ ▷ A)
    π₁β : ∀ {Γ Δ} {A : Ty Δ} (σ : Γ ⇒ Δ) (a : Tm Γ (A [ σ ]t))
        → π₁ A ∘ (σ , a) ≈ σ
    pair-η : ∀ {Γ Δ} {A : Ty Δ} (θ : Γ ⇒ (Δ ▷ A))
           → θ ≈ ((π₁ A ∘ θ) , (let
        w : T.ob Γ .S (Hom.map (T.hom θ) (Hom.map (T.hom (π₁ A)) A))
        w = π₂ A [ θ ]m
        p : {!!}
        u : ∥ T.hom (π₁ A ∘ θ) ≋ comp (T.hom θ) (T.hom (π₁ A)) ∥
        u = {!T.resp !}
        v = {!!} in {!!}) )
    π₂β : ∀ {Γ Δ} {A : Ty Δ} (σ : Γ ⇒ Δ) (a : Tm Γ (A [ σ ]t))
        → (p : (A [ π₁ A ]t) [ (σ , a) ]t ≡ A [ σ ]t)
        → subst (Tm Γ) p (π₂ A [ (σ , a) ]m) ≡ a
