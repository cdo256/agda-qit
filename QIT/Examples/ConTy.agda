module QIT.Examples.ConTy where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset

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
    ≡.cong₂ _▷₁_ (isPropCon₁ Γ₁ Δ₁) {!!}

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

  _₀ = proj₁
  _₁ = proj₂

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

  module RecursionRecursion (D : DisplayedAlgebra) where
    open DisplayedAlgebra D
    elimCon : (Γ : Con) → Conᴰ Γ
    elimTy : {Γ : Con} (A : Ty Γ) → Tyᴰ (elimCon Γ) A

    elimCon (∙₀ , ∙₁) = ∙ᴰ
    elimCon (Γ₀ ▷₀ A₀ , Γ₁ ▷₁ A₁) = elimCon (Γ₀ , Γ₁) ▷ᴰ elimTy (A₀ , A₁)

    elimTy {Γ₀ , Γ₁} (ι₀ Γ₀ , ι₁ Γ₁') =
      ≡.subst (λ ○ → Tyᴰ (elimCon (Γ₀ , Γ₁)) (ι₀ Γ₀ , ι₁ ○)) p u
      where
      p : Γ₁ ≡ Γ₁'
      p = isPropCon₁ Γ₁ Γ₁'
      u : Tyᴰ (elimCon (Γ₀ , Γ₁)) (ι (Γ₀ , Γ₁))
      u = ιᴰ (elimCon (Γ₀ , Γ₁))
    elimTy {Γ₀ , Γ₁} (π₀ Γ₀ A₀ B₀ , π₁ Γ₁' A₁ B₁) =
      ≡.subst (λ ○ → Tyᴰ (elimCon (Γ₀ , Γ₁)) (π₀ Γ₀ A₀ B₀ , π₁ ○ A₁ B₁)) p u
      where
      p : Γ₁ ≡ Γ₁'
      p = isPropCon₁ Γ₁ Γ₁'
      v : Tyᴰ (elimCon (Γ₀ ▷₀ A₀ , Γ₁ ▷₁ A₁)) (B₀ , B₁)
      v = elimTy (B₀ , B₁)
      q : elimCon ((Γ₀ ▷₀ A₀) , (Γ₁ ▷₁ A₁))
        ≡ elimCon (Γ₀ , Γ₁) ▷ᴰ elimTy (A₀ , A₁)
      q = {!!}
      u : Tyᴰ (elimCon (Γ₀ , Γ₁)) (π₀ Γ₀ A₀ B₀ , π₁ Γ₁ A₁ B₁)
      u = πᴰ (elimCon (Γ₀ , Γ₁)) (elimTy (A₀ , A₁)) (subst (λ ○ → Tyᴰ ○ (B₀ , B₁)) q v)

  module _ (D : DisplayedAlgebra) where
    open DisplayedAlgebra D
    data ElimCon : (Γ : Con) → Conᴰ Γ → Set
    data ElimTy : ∀ {Γ Γ̂} (A : Ty Γ) → ElimCon Γ Γ̂ → Tyᴰ Γ̂ A → Set

    data ElimCon where
      e∙ : ElimCon ∙ ∙ᴰ
      e▷ : ∀ {Γ Γ̂ A Â} → (Γᵉ : ElimCon Γ Γ̂) → ElimTy A Γᵉ Â → ElimCon (Γ ▷ A) (Γ̂ ▷ᴰ Â)

    data ElimTy where
      eι : ∀ {Γ Γ̂} → (Γᵉ : ElimCon Γ Γ̂) → ElimTy (ι Γ) Γᵉ (ιᴰ Γ̂)
      eπ : ∀ {Γ Γ̂ A Â B B̂} → (Γᵉ : ElimCon Γ Γ̂)
         → ElimTy A Γᵉ Â → (Δᵉ : ElimCon (Γ ▷ A) (Γ̂ ▷ᴰ Â))
         → ElimTy B Δᵉ B̂ → ElimTy (π Γ A B) Γᵉ (πᴰ Γ̂ Â B̂)

    isContrElimCon : ∀ Γ → isContr (Σ _ (ElimCon Γ))
    isContrElimTy : ∀ {Γ Γ̂} (A : Ty Γ) → (Γᵉ : ElimCon Γ Γ̂) → isContr (Σ _ (ElimTy A Γᵉ))

    Con-∃ : ∀ (Γ : Con) → Σ _ λ Γ̂ → ElimCon Γ Γ̂
    Ty-∃ : ∀ {Γ Γ̂} (A : Ty Γ) → (Γᵉ : ElimCon Γ Γ̂) → Σ _ λ Aᵉ → ElimTy A Γᵉ Aᵉ
    Con-∃! : ∀ (Γ : Con) → ∀ Γ̂ → ElimCon Γ Γ̂ → proj₁ (Con-∃ Γ) ≡ Γ̂
    Ty-∃! : ∀ {Γ Γ̂} (A : Ty Γ) → (Γᵉ : ElimCon Γ Γ̂) → ∀ Aᵉ → ElimTy A Γᵉ Aᵉ → proj₁ (Ty-∃ A Γᵉ) ≡ Aᵉ 

    Con-∃ (∙₀ , ∙₁) = ∙ᴰ , e∙
    Con-∃ ((Γ₀ ▷₀ A₀) , (Γ₁ ▷₁ A₁)) = 
      let Γ̂ , Γᵉ = Con-∃ (Γ₀ , Γ₁)
          Â , Aᵉ = Ty-∃ (A₀ , A₁) Γᵉ
      in (Γ̂ ▷ᴰ Â) , e▷ Γᵉ Aᵉ

    Ty-∃ {Γ₀ , Γ₁} {Γ̂ = Γ̂} (ι₀ Γ₀ , ι₁ Γ₁') Γᵉ' with isPropCon₁ Γ₁ Γ₁'
    ... | ≡.refl = ιᴰ Γ̂  , eι Γᵉ'
    Ty-∃ {Γ₀ , Γ₁} {Γ̂ = Γ̂} (π₀ Γ₀ A₀ B₀ , π₁ Γ₁' A₁ B₁) Γᵉ
      with isPropCon₁ Γ₁ Γ₁' 
    ... | ≡.refl =
      let Â , Aᵉ = Ty-∃ (A₀ , A₁) Γᵉ
          Δ̂ , Δᵉ = Con-∃ ((Γ₀ , Γ₁) ▷ (A₀ , A₁))
          B̂ , Bᵉ = Ty-∃ (B₀ , B₁) Δᵉ
          p : Δ̂ ≡ Δ̂
          p = Con-∃! ((Γ₀ , Γ₁) ▷ (A₀ , A₁)) Δ̂ Δᵉ
      in πᴰ Γ̂ Â {!B̂!} , {!!}
