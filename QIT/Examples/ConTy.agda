module QIT.Examples.ConTy where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.WellFounded

module Plain where
  data Con : Set
  data Ty : Con → Set

  data Con where
    ∙ : Con
    _▷_ : (Γ : Con) → Ty Γ → Con

  data Ty where
    ι : (Γ : Con) → Ty Γ
    Π̇ : (Γ : Con) → (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ

module Erased where
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
    ≡cong₃ π₁ (isPropCon₁ Γ₁ Δ₁) (isPropTy₁ A₁ C₁) (isPropTy₁ B₁ D₁)

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
  record DisplayedAlgebra : Set₁ where
    field
      Conᴰ : Con → Set
      Tyᴰ : {Γ : Con} → Conᴰ Γ → Ty Γ → Set
      ∙ᴰ : Conᴰ ∙
      _▷ᴰ_ : ∀ {Γ A} (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ A → Conᴰ (Γ ▷ A)
      ιᴰ : ∀ {Γ} (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ (ι Γ)
      πᴰ : ∀ {Γ A B} (Γᴰ : Conᴰ Γ) (Aᴰ : Tyᴰ Γᴰ A) (Bᴰ : Tyᴰ (Γᴰ ▷ᴰ Aᴰ) B)
         → Tyᴰ Γᴰ (π Γ A B)

  -- module RecursionRecursion (D : DisplayedAlgebra) where
  --   open DisplayedAlgebra D
  --   elimCon : (Γ : Con) → Conᴰ Γ
  --   elimTy : {Γ : Con} (A : Ty Γ) → Tyᴰ (elimCon Γ) A

  --   elimCon (∙₀ , ∙₁) = ∙ᴰ
  --   elimCon (Γ₀ ▷₀ A₀ , Γ₁ ▷₁ A₁) = elimCon (Γ₀ , Γ₁) ▷ᴰ elimTy (A₀ , A₁)

  --   elimTy {Γ₀ , Γ₁} (ι₀ Γ₀ , ι₁ Γ₁') =
  --     ≡.subst (λ ○ → Tyᴰ (elimCon (Γ₀ , Γ₁)) (ι₀ Γ₀ , ι₁ ○)) p u
  --     where
  --     p : Γ₁ ≡ Γ₁'
  --     p = isPropCon₁ Γ₁ Γ₁'
  --     u : Tyᴰ (elimCon (Γ₀ , Γ₁)) (ι (Γ₀ , Γ₁))
  --     u = ιᴰ (elimCon (Γ₀ , Γ₁))
  --   elimTy {Γ₀ , Γ₁} (π₀ Γ₀ A₀ B₀ , π₁ Γ₁' A₁ B₁) =
  --     ≡.subst (λ ○ → Tyᴰ (elimCon (Γ₀ , Γ₁)) (π₀ Γ₀ A₀ B₀ , π₁ ○ A₁ B₁)) p u
  --     where
  --     p : Γ₁ ≡ Γ₁'
  --     p = isPropCon₁ Γ₁ Γ₁'
  --     v : Tyᴰ (elimCon (Γ₀ ▷₀ A₀ , Γ₁ ▷₁ A₁)) (B₀ , B₁)
  --     v = elimTy (B₀ , B₁)
  --     q : elimCon ((Γ₀ ▷₀ A₀) , (Γ₁ ▷₁ A₁))
  --       ≡ elimCon (Γ₀ , Γ₁) ▷ᴰ elimTy (A₀ , A₁)
  --     q = {!!}
  --     u : Tyᴰ (elimCon (Γ₀ , Γ₁)) (π₀ Γ₀ A₀ B₀ , π₁ Γ₁ A₁ B₁)
  --     u = πᴰ (elimCon (Γ₀ , Γ₁)) (elimTy (A₀ , A₁)) (subst (λ ○ → Tyᴰ ○ (B₀ , B₁)) q v)

  module _ (D : DisplayedAlgebra) where
    open DisplayedAlgebra D
    data ElimCon : (Γ : Con) → Conᴰ Γ → Set
    data ElimTy : ∀ {Γ} (Γ̂ : Conᴰ Γ) (A : Ty Γ) → Tyᴰ Γ̂ A → Set

    data ElimCon where
      e∙ : ElimCon ∙ ∙ᴰ
      e▷ : ∀ {Γ Γ̂ A Â} → (Γᵉ : ElimCon Γ Γ̂) → ElimTy Γ̂ A Â → ElimCon (Γ ▷ A) (Γ̂ ▷ᴰ Â)

    data ElimTy where
      eι : ∀ {Γ Γ̂} → (Γᵉ : ElimCon Γ Γ̂) → ElimTy Γ̂ (ι Γ) (ιᴰ Γ̂)
      eπ : ∀ {Γ Γ̂ A Â B B̂} → (Γᵉ : ElimCon Γ Γ̂)
         → ElimTy Γ̂ A Â → (Δᵉ : ElimCon (Γ ▷ A) (Γ̂ ▷ᴰ Â))
         → ElimTy (Γ̂ ▷ᴰ Â) B B̂ → ElimTy Γ̂ (π Γ A B) (πᴰ Γ̂ Â B̂)


    data ConTy₀ : Set ℓ0 where
      con : Con₀ → ConTy₀
      ty : Ty₀ → ConTy₀
      
    data ConTy : Set ℓ0 where
      con : Con → ConTy
      ty : {Γ : Con} → Ty Γ → ConTy

    ConTyFst : ConTy → ConTy₀
    ConTyFst (con (Γ₀ , _)) = con Γ₀
    ConTyFst (ty (A₀ , _)) = ty A₀

    data _<₀_ : ConTy₀ → ConTy₀ → Set (lsuc ℓ0) where
      <▷₀-1 : ∀ Γ A → con Γ <₀ con (Γ ▷₀ A)
      <▷₀-2 : ∀ Γ A → ty A <₀ con (Γ ▷₀ A)
      <ι₀-1 : ∀ Γ → con Γ <₀ ty (ι₀ Γ)
      <π₀-1 : ∀ Γ A B → con Γ <₀ ty (π₀ Γ A B)
      <π₀-2 : ∀ Γ A B → ty A <₀ ty (π₀ Γ A B)
      <π₀-3 : ∀ Γ A B → ty B <₀ ty (π₀ Γ A B)
      <<₀ : ∀ x y z → x <₀ y → y <₀ z → x <₀ z

    _<_ : ConTy → ConTy → Set (lsuc ℓ0) 
    x < y = ConTyFst x <₀ ConTyFst y

    access : ∀ {x} → Acc _<₀_ x → ∀ y → _<₀_ y x → Acc _<₀_ y
    access (acc rs) y y<x = rs y y<x

    <₀-wf : WellFounded _<₀_
    r-con : ∀ Γ → WfRec _<₀_ (Acc _<₀_) (con Γ)
    r-ty : ∀ A → WfRec _<₀_ (Acc _<₀_) (ty A)

    <₀-wf (con Γ) = acc (r-con Γ)
    <₀-wf (ty A)  = acc (r-ty A)

    r-con _ _ (<▷₀-1 Γ A) = <₀-wf (con Γ)
    r-con _ _ (<▷₀-2 Γ A) = <₀-wf (ty A)
    r-con _ _ (<<₀ x y (con Γ) x<y y<Γ) =
      access (r-con Γ y y<Γ) x x<y

    r-ty _ _ (<ι₀-1 Γ) = <₀-wf (con Γ)
    r-ty _ _ (<π₀-1 Γ A B) = <₀-wf (con Γ)
    r-ty _ _ (<π₀-2 Γ A B) = <₀-wf (ty A)
    r-ty _ _ (<π₀-3 Γ A B) = <₀-wf (ty B)
    r-ty _ _ (<<₀ x y (ty A) x<y y<A) =
      access (r-ty A y y<A) x x<y

    <-wf : WellFounded _<_
    <-wf = wfProj _<₀_ ConTyFst <₀-wf

    ConTy-∃-Type : ConTy → Set
    ConTy-∃-Type (con Γ) = Σ (Conᴰ Γ) (ElimCon Γ)
    ConTy-∃-Type (ty {Γ} A) = ∀ {Γ̂} → ElimCon Γ Γ̂ → Σ (Tyᴰ Γ̂ A) (ElimTy Γ̂ A)

    ConTy-∃-step : ∀ x → (∀ y → y < x → ConTy-∃-Type y) → ConTy-∃-Type x
    ConTy-∃-step (con (∙₀ , ∙₁)) rec = ∙ᴰ , e∙
    ConTy-∃-step (con (Γ₀ ▷₀ A₀ , Γ₁ ▷₁ A₁)) rec =
      let (Γ̂ , Γᵉ) = rec (con (Γ₀ , Γ₁)) (<▷₀-1 _ _)
          (Â , Aᵉ) = rec (ty (A₀ , A₁)) (<▷₀-2 _ _) Γᵉ
      in (Γ̂ ▷ᴰ Â) , e▷ Γᵉ Aᵉ
    ConTy-∃-step (ty {Γ₀ , Γ₁} (ι₀ Γ₀ , ι₁ Γ₁')) rec {Γ̂} Γᵉ
      with isPropCon₁ Γ₁ Γ₁'
    ... | ≡.refl = ιᴰ Γ̂ , eι Γᵉ 
    ConTy-∃-step (ty {Γ₀ , Γ₁} (π₀ Γ₀ A₀ B₀ , π₁ Γ₁' A₁ B₁)) rec {Γ̂} Γᵉ
      with isPropCon₁ Γ₁ Γ₁'
    ... | ≡.refl =
      let (Â , Aᵉ) = rec (ty (A₀ , A₁)) (<π₀-2 _ _ _) Γᵉ
          (B̂ , Bᵉ) = rec (ty (B₀ , B₁)) (<π₀-3 _ _ _) (e▷ Γᵉ Aᵉ)
      in πᴰ Γ̂ Â B̂ , eπ Γᵉ Aᵉ (e▷ Γᵉ Aᵉ) Bᵉ

    Con-∃ : ∀ Γ → Σ (Conᴰ Γ) (ElimCon Γ)
    Con-∃ Γ = Wf-ind _<_ <-wf ConTy-∃-Type ConTy-∃-step (con Γ)

    Ty-∃ : ∀ {Γ Γ̂} (A : Ty Γ) → ElimCon Γ Γ̂ → Σ (Tyᴰ Γ̂ A) (ElimTy Γ̂ A)
    Ty-∃ A = Wf-ind _<_ <-wf ConTy-∃-Type ConTy-∃-step (ty A)

    ConTy-∃!-Type : ConTy → Set
    ConTy-∃!-Type (con Γ) = ∀ Γ̂ → ElimCon Γ Γ̂ → proj₁ (Con-∃ Γ) ≡ Γ̂
    ConTy-∃!-Type (ty {Γ} A) =
      ∀ {Γ̂} → (Γᵉ : ElimCon Γ Γ̂) → (Â : Tyᴰ Γ̂ A) → ElimTy Γ̂ A Â
      → proj₁ (Ty-∃ A Γᵉ) ≡ Â

    ConTy-∃!-step : ∀ x → (∀ y → y < x → ConTy-∃!-Type y) → ConTy-∃!-Type x
    ConTy-∃!-step (con (∙₀ , ∙₁)) rec Γ̂ e∙ = ≡.refl
    ConTy-∃!-step (con ((Γ₀ ▷₀ A₀) , (Γ₁ ▷₁ A₁))) rec Δ̂ (e▷ {Γ̂ = Γ̂} {Â = Â} Γᵉ Aᵉ) =
      let Γ̂' , Γᵉ'  = Con-∃ ((Γ₀ ▷₀ A₀) , (Γ₁ ▷₁ A₁))
          pΓ = rec (con (Γ₀ , Γ₁)) (<▷₀-1 _ _) Γ̂ Γᵉ
          pA = rec (ty (A₀ , A₁)) (<▷₀-2 _ _) Γᵉ Â Aᵉ
      in {!≡congp₂ _▷ᴰ_ {!!} {!!}!}

    -- ConTy-∃!-step (ty {Γ₀ , Γ₁} (ι₀ Γ₀ , ι₁ Γ₁')) rec {Γ̂} Γᵉ
    --   with isPropCon₁ Γ₁ Γ₁'
    -- ... | ≡.refl = ιᴰ Γ̂ , eι Γᵉ 
    -- ConTy-∃!-step (ty {Γ₀ , Γ₁} (π₀ Γ₀ A₀ B₀ , π₁ Γ₁' A₁ B₁)) rec {Γ̂} Γᵉ
    --   with isPropCon₁ Γ₁ Γ₁'
    -- ... | ≡.refl =
    --   let (Â , Aᵉ) = rec (ty (A₀ , A₁)) (<π₀-2 _ _ _) Γᵉ
    --       (B̂ , Bᵉ) = rec (ty (B₀ , B₁)) (<π₀-3 _ _ _) (e▷ Γᵉ Aᵉ)
    --   in πᴰ Γ̂ Â B̂ , eπ Γᵉ Aᵉ (e▷ Γᵉ Aᵉ) Bᵉ

    -- -- Con-∃! : ∀ (Γ : Con) → ∀ Γ̂ → (Γᵉ : ElimCon Γ Γ̂)
    -- --        → proj₁ (Con-∃ Γ) ≡ Γ̂
    -- -- Con-∃! Γ = Wf-ind _<_ <-wf {!ConTy-∃!-Type!} {!!} {!!}

    -- -- Ty-∃! : ∀ {Γ Γ̂} (A : Ty Γ) → (Γᵉ : ElimCon Γ Γ̂) → (Â : Tyᴰ Γ̂ A) → (Aᵉ : ElimTy Γ̂ A Â)
    -- --       → proj₁ (Ty-∃ A Γᵉ) ≡ Â
