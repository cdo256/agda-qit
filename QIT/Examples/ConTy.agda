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

    ElimConΣ : (Γ : Con) → Set 
    ElimConΣ Γ = Σ (Conᴰ Γ) (ElimCon Γ)

    ElimConΣ≡ : {Γ : Con} (ΓΣ ΓΣ' : ElimConΣ Γ) → Set
    ElimConΣ≡ (Γ̂ , _) (Γ̂' , _) = Γ̂ ≡ Γ̂'
  
    ElimTyΣ : {Γ : Con} (A : Ty Γ) → ElimConΣ Γ → Set
    ElimTyΣ A (Γ̂ , _) = Σ (Tyᴰ Γ̂ A) (ElimTy Γ̂ A)

    ElimTyΣ≡ : {Γ : Con} {A : Ty Γ} (ΓΣ ΓΣ' : ElimConΣ Γ) (p : ElimConΣ≡ ΓΣ ΓΣ')
             → (AΣ : ElimTyΣ A ΓΣ) (AΣ' : ElimTyΣ A ΓΣ') → Set
    ElimTyΣ≡ {A = A} ΓΣ ΓΣ' p (Â , Aᵉ) (Â' , Aᵉ') = subst (λ ○ → Tyᴰ ○ A) p Â ≡ Â'

    data ConTy₀ : Set where
      con : Con₀ → ConTy₀
      ty : Ty₀ → ConTy₀
      
    data ConTy : Set where
      con : Con → ConTy
      ty : {Γ : Con} → Ty Γ → ConTy

    ConTyFst : ConTy → ConTy₀
    ConTyFst (con (Γ₀ , _)) = con Γ₀
    ConTyFst (ty (A₀ , _)) = ty A₀

    mutual
      Con-∃-∙ : ElimConΣ ∙
      Con-∃-∙ = ∙ᴰ , e∙
      Con-∃-▷ : {Γ : Con} (ΓΣ : ElimConΣ Γ)
              → {A : Ty Γ} (AΣ : ElimTyΣ A ΓΣ)
              → ElimConΣ (Γ ▷ A)
      Con-∃-▷ (Γ̂ , Γᵉ) (Â , Aᵉ) =
        (Γ̂ ▷ᴰ Â) , e▷ Γᵉ Aᵉ

      Ty-∃-ι : {Γ₀ : Con₀} (Γ₁ Γ₁' : Con₁ Γ₀) (pΓ₁ : Γ₁ ≡ Γ₁') (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
             → ElimTyΣ (ι (Γ₀ , Γ₁')) ΓΣ
      Ty-∃-ι {Γ₀} Γ₁ .Γ₁ ≡.refl (Γ̂ , Γᵉ) = ιᴰ Γ̂ , eι Γᵉ

      Ty-∃-π : {Γ₀ : Con₀} {Γ₁ Γ₁' : Con₁ Γ₀} (pΓ₁ : Γ₁ ≡ Γ₁') (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
             → {A : Ty (Γ₀ , Γ₁)} (AΣ : ElimTyΣ A ΓΣ)
             → (ΔΣ : ElimConΣ ((Γ₀ , Γ₁) ▷ A))
             → {B : Ty ((Γ₀ , Γ₁) ▷ A)} (BΣ : ElimTyΣ B (Con-∃-▷ ΓΣ AΣ))
             → ElimTyΣ (π (Γ₀ , Γ₁') A B) ΓΣ
      Ty-∃-π ≡.refl (Γ̂ , Γᵉ) (Â , Aᵉ) (Δ̂ , Δᵉ) (B̂ , Bᵉ) =
             πᴰ Γ̂ Â B̂ , eπ Γᵉ Aᵉ (e▷ Γᵉ Aᵉ) Bᵉ
             
      Con-∃-rec : (Γ₀ : Con₀) (Γ₁ : Con₁ Γ₀)
                → ElimConΣ (Γ₀ , Γ₁)
      Con-∃-rec ∙₀ ∙₁ =
        Con-∃-∙
      Con-∃-rec (Γ₀ ▷₀ A₀) (Γ₁ ▷₁ A₁) =
        Con-∃-▷ (Con-∃-rec Γ₀ Γ₁) (Ty-∃-rec A₀ A₁ (Con-∃-rec Γ₀ Γ₁))

      Ty-∃-rec : {Γ₀ : Con₀} {Γ₁ : Con₁ Γ₀} (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀)
               → (ΓΣ : ElimConΣ (Γ₀ , Γ₁)) → ElimTyΣ (A₀ , A₁) ΓΣ
      Ty-∃-rec {Γ₀} {Γ₁} (ι₀ Γ₀) (ι₁ Γ₁') (Γ̂ , Γᵉ) =
        Ty-∃-ι Γ₁ Γ₁' (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ)
      Ty-∃-rec {Γ₀} {Γ₁} (π₀ Γ₀ A₀ B₀) (π₁ Γ₁' A₁ B₁) (Γ̂ , Γᵉ) =
        Ty-∃-π (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ)
               (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ))
               (Con-∃-rec (Γ₀ ▷₀ A₀) (Γ₁ ▷₁ A₁))
               (Ty-∃-rec B₀ B₁ (Con-∃-▷ (Γ̂ , Γᵉ) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ))))

    Con-∃ : (Γ : Con) → ElimConΣ Γ
    Con-∃ (Γ₀ , Γ₁) = Con-∃-rec Γ₀ Γ₁
    
    Ty-∃ : {Γ : Con} → (A : Ty Γ) → ElimTyΣ A (Con-∃ Γ)
    Ty-∃ {Γ} (A₀ , A₁) = Ty-∃-rec A₀ A₁ (Con-∃ Γ)

    mutual
      Con-∃!-▷ : (Γ : Con) (ΓΣ : ElimConΣ Γ)
               → (A : Ty Γ) (AΣ : ElimTyΣ A ΓΣ)
               → (ΔΣ : ElimConΣ (Γ ▷ A))
               → (pΓ : ElimConΣ≡ (Con-∃ Γ) ΓΣ)
               → (pA : ElimTyΣ≡ (Con-∃ Γ) ΓΣ pΓ (Ty-∃ A) AΣ)
               → ElimConΣ≡ (Con-∃ (Γ ▷ A)) ΔΣ 
      Con-∃!-▷ (Γ₀ , Γ₁) (Γ̂ , Γᵉ)
               (A₀ , A₁) (Â , Aᵉ)
               (Δ̂ , e▷ {Γ̂ = Γ̂'} {Â = Â'} Γᵉ' Aᵉ') ≡.refl ≡.refl =
        ≡.dcong₂ _▷ᴰ_ (Con-∃!-rec Γ₀ Γ₁ (Γ̂' , Γᵉ')) (Ty-∃!-rec (Γ̂' , Γᵉ') A₀ A₁ (Â' , Aᵉ'))
      

      Ty-∃-ι-q-irrel : {Γ₀ : Con₀} {Γ₁ Γ₁' : Con₁ Γ₀} (q : Γ₁ ≡ Γ₁') (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
                    → proj₁ (Ty-∃-ι Γ₁ Γ₁' q ΓΣ)
                    ≡ subst (λ ○ → Tyᴰ (proj₁ ΓΣ) (ι₀ Γ₀ , ι₁ ○)) q (ιᴰ (proj₁ ΓΣ))
      Ty-∃-ι-q-irrel ≡.refl (Γ̂ , Γᵉ) = ≡.refl

      Ty-∃-ι-irrel
        : {Γ₀ : Con₀} {Γ₁ Γ₁' : Con₁ Γ₀} 
        → (q : Γ₁ ≡ Γ₁') 
        → (ΓΣ ΓΣ' : ElimConΣ (Γ₀ , Γ₁))
        → (p : ElimConΣ≡ ΓΣ ΓΣ')
        → ElimTyΣ≡ ΓΣ ΓΣ' p (Ty-∃-ι Γ₁ Γ₁' q ΓΣ) (Ty-∃-ι Γ₁ Γ₁' q ΓΣ')
      Ty-∃-ι-irrel ≡.refl (Γ̂ , Γᵉ) (.Γ̂ , Γᵉ') ≡.refl = ≡.refl

      Con-∃!-rec : (Γ₀ : Con₀) (Γ₁ : Con₁ Γ₀)
                 → (ΓΣ : ElimConΣ (Γ₀ , Γ₁)) → ElimConΣ≡ (Con-∃ (Γ₀ , Γ₁)) ΓΣ 
      Con-∃!-rec ∙₀ ∙₁ (Γ̂ , e∙) = ≡.refl
      Con-∃!-rec (Γ₀ ▷₀ A₀) (Γ₁ ▷₁ A₁) (Δ̂ , e▷ {Γ̂ = Γ̂'} {Â = Â'} Γᵉ Aᵉ) =
        Con-∃!-▷ (Γ₀ , Γ₁) (Γ̂' , Γᵉ) (A₀ , A₁) (Â' , Aᵉ) ((Γ̂' ▷ᴰ Â') , e▷ Γᵉ Aᵉ)
                 (Con-∃!-rec Γ₀ Γ₁ (Γ̂' , Γᵉ))
                 (Ty-∃!-rec (Γ̂' , Γᵉ) A₀ A₁ (Â' , Aᵉ))

      Ty-∃!-ι
        : (Γ₀ : Con₀) (Γ₁ Γ₁' : Con₁ Γ₀) (pΓ : Γ₁ ≡ Γ₁')
        → (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
        → (AΣ : ElimTyΣ (ι (Γ₀ , Γ₁')) ΓΣ)
        → ElimTyΣ≡ (Con-∃ (Γ₀ , Γ₁)) ΓΣ (Con-∃!-rec Γ₀ Γ₁ ΓΣ)
                   (Ty-∃ (ι (Γ₀ , Γ₁'))) AΣ
      Ty-∃!-ι Γ₀ Γ₁ Γ₁ ≡.refl (Γ̂ , Γᵉ) (Â , Aᵉ@(eι Γᵉ')) =
        subst (λ ○ → Tyᴰ ○ (ι₀ Γ₀ , ι₁ Γ₁)) (Con-∃!-rec Γ₀ Γ₁ (Γ̂ , Γᵉ))
              (proj₁ (Ty-∃ (ι₀ Γ₀ , ι₁ Γ₁)))
          ≡⟨ Ty-∃-irrel (ι₀ Γ₀) (ι₁ Γ₁) (Con-∃ (Γ₀ , Γ₁)) (Γ̂ , Γᵉ) (Con-∃!-rec Γ₀ Γ₁ (Γ̂ , Γᵉ)) ⟩
        proj₁ (Ty-∃-rec (ι₀ Γ₀) (ι₁ Γ₁) (Γ̂ , Γᵉ))
          ≡⟨ ≡.refl ⟩
        proj₁ (Ty-∃-ι Γ₁ Γ₁ (isPropCon₁ Γ₁ Γ₁) (Γ̂ , Γᵉ))
          ≡⟨ Ty-∃-ι-q-irrel (isPropCon₁ Γ₁ Γ₁) (Γ̂ , Γᵉ) ⟩
        subst (λ ○ → Tyᴰ Γ̂ (ι₀ Γ₀ , ι₁ ○)) (isPropCon₁ Γ₁ Γ₁) (ιᴰ Γ̂)
          ≡⟨ ≡.cong (λ □ → subst (λ ○ → Tyᴰ Γ̂ (ι₀ Γ₀ , ι₁ ○)) □ (ιᴰ Γ̂))
                    (isSetSet (isPropCon₁ Γ₁ Γ₁) ≡.refl) ⟩
        ιᴰ Γ̂
          ≡⟨ ≡.refl ⟩
        Â ∎
        where
        open ≡.≡-Reasoning
 
      Ty-∃!-rec : {Γ₀ : Con₀} {Γ₁ : Con₁ Γ₀} (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
                → (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀) (AΣ : ElimTyΣ (A₀ , A₁) ΓΣ)
                → ElimTyΣ≡ (Con-∃ (Γ₀ , Γ₁)) ΓΣ (Con-∃!-rec Γ₀ Γ₁ ΓΣ)
                           (Ty-∃ (A₀ , A₁)) AΣ
      Ty-∃!-rec {Γ₀} {Γ₁} (Γ̂ , Γᵉ) (ι₀ Γ₀) (ι₁ Γ₁') (Â , Aᵉ) =
        Ty-∃!-ι Γ₀ Γ₁ Γ₁' (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ) (Â , Aᵉ)
      Ty-∃!-rec (Δ̂ , Δᵉ) (π₀ Γ₀ A₀ B₀) (π₁ Γ₁ A₁ B₁) (Â , eπ Γᵉ' Aᵉ' Δᵉ' Bᵉ') =
        {!Ty-∃!-π!}

      Con-∃!-▷-step
        : {Γ₀ : Con₀} {Γ₁ Γ₁' : Con₁ Γ₀}
        → (q : Γ₁ ≡ Γ₁')
        → (ΓΣ ΓΣ' : ElimConΣ (Γ₀ , Γ₁))
        → (p : ElimConΣ≡ ΓΣ ΓΣ')
        → (A : Ty (Γ₀ , Γ₁)) (AΣ : ElimTyΣ A ΓΣ) (AΣ' : ElimTyΣ A ΓΣ')
        → (pA : ElimTyΣ≡ ΓΣ ΓΣ' p AΣ AΣ')
        → ElimConΣ≡ (Con-∃-▷ ΓΣ AΣ) (Con-∃-▷ ΓΣ' AΣ')
      Con-∃!-▷-step ≡.refl ΓΣ ΓΣ' ≡.refl A AΣ AΣ' ≡.refl = ≡.refl

      Ty-∃-π-irrel
        : {Γ₀ : Con₀} {Γ₁ Γ₁' : Con₁ Γ₀}
        → (q : Γ₁ ≡ Γ₁')
        → (ΓΣ ΓΣ' : ElimConΣ (Γ₀ , Γ₁))
        → (p : ElimConΣ≡ ΓΣ ΓΣ')
        → (A : Ty (Γ₀ , Γ₁)) (AΣ : ElimTyΣ A ΓΣ) (AΣ' : ElimTyΣ A ΓΣ')
        → (pA : ElimTyΣ≡ ΓΣ ΓΣ' p AΣ AΣ')
        → (B : Ty ((Γ₀ , Γ₁) ▷ A))
        → (BΣ : ElimTyΣ B (Con-∃-▷ ΓΣ AΣ))
        → (BΣ' : ElimTyΣ B (Con-∃-▷ ΓΣ' AΣ'))
        → (pB : ElimTyΣ≡ (Con-∃-▷ ΓΣ AΣ)
                         (Con-∃-▷ ΓΣ' AΣ')
                         (Con-∃!-▷-step q ΓΣ ΓΣ' p A AΣ AΣ' pA)
                         BΣ BΣ')
        → ElimTyΣ≡ ΓΣ ΓΣ' p
                   (Ty-∃-π q ΓΣ AΣ (Con-∃-▷ ΓΣ AΣ) BΣ)
                   (Ty-∃-π q ΓΣ' AΣ' (Con-∃-▷ ΓΣ' AΣ') BΣ')
      Ty-∃-π-irrel
        ≡.refl (Γ̂ , Γᵉ) (.Γ̂ , Γᵉ') ≡.refl A (Â , Aᵉ) (.Â , Aᵉ')
        ≡.refl B (B̂ , Bᵉ) (.B̂ , Bᵉ') ≡.refl = ≡.refl

      Ty-∃-irrel : {Γ₀ : Con₀} {Γ₁ : Con₁ Γ₀} (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀) 
                 → (ΓΣ ΓΣ' : ElimConΣ (Γ₀ , Γ₁)) (pΓ : ElimConΣ≡ ΓΣ ΓΣ')
                 → ElimTyΣ≡ ΓΣ ΓΣ' pΓ (Ty-∃-rec A₀ A₁ ΓΣ) (Ty-∃-rec A₀ A₁ ΓΣ')
      Ty-∃-irrel {Γ₀} {Γ₁} (ι₀ Γ₀) (ι₁ Γ₁') (Γ̂ , Γᵉ) (Γ̂ , Γᵉ') ≡.refl =
        Ty-∃-ι-irrel (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ) (Γ̂ , Γᵉ') ≡.refl
      Ty-∃-irrel {Γ₀} {Γ₁} (π₀ Γ₀ A₀ B₀) (π₁ Γ₁' A₁ B₁) (Γ̂ , Γᵉ) (Γ̂ , Γᵉ') ≡.refl =
        Ty-∃-π-irrel (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ) (Γ̂ , Γᵉ') ≡.refl (A₀ , A₁) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ)) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ')) (Ty-∃-irrel A₀ A₁ (Γ̂ , Γᵉ) (Γ̂ , Γᵉ') ≡.refl) (B₀ , B₁) (Ty-∃-rec B₀ B₁ (Con-∃-▷ (Γ̂ , Γᵉ) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ)))) (Ty-∃-rec B₀ B₁ (Con-∃-▷ (Γ̂ , Γᵉ') (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ')))) (Ty-∃-irrel B₀ B₁ (Con-∃-▷ (Γ̂ , Γᵉ) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ))) (Con-∃-▷ (Γ̂ , Γᵉ') (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ')))
        (Con-∃!-▷-step (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ) (Γ̂ , Γᵉ') ≡.refl
                       (A₀ , A₁) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ))
                       (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ'))
                       (Ty-∃-irrel A₀ A₁ (Γ̂ , Γᵉ) (Γ̂ , Γᵉ') ≡.refl)))

      Ty-∃-π-q-irrel : {Γ₀ : Con₀} {Γ₁ Γ₁' : Con₁ Γ₀} (q : Γ₁ ≡ Γ₁') (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
                      (A : Ty (Γ₀ , Γ₁)) (AΣ : ElimTyΣ A ΓΣ)
                      (ΔΣ : ElimConΣ ((Γ₀ , Γ₁) ▷ A))
                      (B : Ty ((Γ₀ , Γ₁) ▷ A)) (BΣ : ElimTyΣ B (Con-∃-▷ ΓΣ AΣ))
                    → proj₁ (Ty-∃-π q ΓΣ AΣ ΔΣ BΣ)
                    ≡ subst (λ ○ → Tyᴰ (proj₁ ΓΣ) (π₀ Γ₀ (proj₁ A) (proj₁ B) , π₁ ○ (proj₂ A) (proj₂ B))) q (πᴰ (proj₁ ΓΣ) (proj₁ AΣ) (proj₁ BΣ))
      Ty-∃-π-q-irrel ≡.refl ΓΣ A AΣ ΔΣ B BΣ = ≡.refl

      trans-ElimTyΣ : {Γ : Con} {A : Ty Γ} (ΓΣ ΓΣ' : ElimConΣ Γ)
                    → (p : ElimConΣ≡ ΓΣ ΓΣ') → ElimTyΣ A ΓΣ → ElimTyΣ A ΓΣ'
      trans-ElimTyΣ (Γ̂ , Γᵉ) (.Γ̂ , Γᵉ') ≡.refl (Â , Aᵉ) = Â , Aᵉ

      trans-ElimTyΣ-refl : {Γ : Con} {A : Ty Γ} (ΓΣ : ElimConΣ Γ) 
                         → (AΣ : ElimTyΣ A ΓΣ) → trans-ElimTyΣ ΓΣ ΓΣ ≡.refl AΣ ≡ AΣ
      trans-ElimTyΣ-refl ΓΣ AΣ = ≡.refl

      Ty-∃!-π
        : {Γ₀ : Con₀} {Γ₁ Γ₁' : Con₁ Γ₀} (q : Γ₁ ≡ Γ₁')
        → (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
        → (A : Ty (Γ₀ , Γ₁)) (B : Ty ((Γ₀ , Γ₁) ▷ A))
        → (AΣ : ElimTyΣ A ΓΣ) (ΔΣ : ElimConΣ ((Γ₀ , Γ₁) ▷ A)) (BΣ : ElimTyΣ B ΔΣ)
        → (pA : ElimTyΣ≡ (Con-∃ (Γ₀ , Γ₁)) ΓΣ (Con-∃!-rec Γ₀ Γ₁ ΓΣ) (Ty-∃ A) AΣ)
        → (pΔ : ElimConΣ≡ (Con-∃ ((Γ₀ , Γ₁) ▷ A)) ΔΣ)
        → (pB : ElimTyΣ≡ (Con-∃ ((Γ₀ , Γ₁) ▷ A)) ΔΣ pΔ (Ty-∃ B) BΣ)
        → ElimTyΣ≡ (Con-∃ (Γ₀ , Γ₁)) ΓΣ (Con-∃!-rec Γ₀ Γ₁ ΓΣ)
                   (Ty-∃ (π (Γ₀ , Γ₁') A B))
                   (Ty-∃-π q ΓΣ AΣ ΔΣ (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ AΣ)))
      Ty-∃!-π {Γ₀} {Γ₁} {Γ₁'} ≡.refl ΓΣ A B AΣ ΔΣ BΣ ≡.refl ≡.refl ≡.refl =
        let pΓ = Con-∃!-rec Γ₀ Γ₁ ΓΣ
        in 
        subst (λ ○ → Tyᴰ ○ (π (Γ₀ , Γ₁') A B)) pΓ (proj₁ (Ty-∃ (π (Γ₀ , Γ₁') A B)))
          ≡⟨ Ty-∃-irrel (π₀ Γ₀ (proj₁ A) (proj₁ B)) (π₁ Γ₁' (proj₂ A) (proj₂ B)) (Con-∃ (Γ₀ , Γ₁)) ΓΣ pΓ ⟩
        proj₁ (Ty-∃-rec (π₀ Γ₀ (proj₁ A) (proj₁ B)) (π₁ Γ₁' (proj₂ A) (proj₂ B)) ΓΣ)
          ≡⟨ ≡.refl ⟩
        proj₁ (Ty-∃-π (isPropCon₁ Γ₁ Γ₁') ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ) ΔΣ
              (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ ))))
          ≡⟨ Ty-∃-π-q-irrel (isPropCon₁ Γ₁ Γ₁') ΓΣ A (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ) (Con-∃-rec _ _) B (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ))) ⟩
        subst (λ ○ → Tyᴰ (proj₁ ΓΣ) (π₀ Γ₀ (proj₁ A) (proj₁ B) , π₁ ○ (proj₂ A) (proj₂ B))) (isPropCon₁ Γ₁ Γ₁) (πᴰ (proj₁ ΓΣ) (proj₁ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ)) (proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) ((Con-∃-▷ ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ))))))
          ≡⟨ substDefEq (λ ○ → Tyᴰ (proj₁ ΓΣ) (π₀ Γ₀ (proj₁ A) (proj₁ B) , π₁ ○ (proj₂ A) (proj₂ B))) (isPropCon₁ Γ₁ Γ₁) (πᴰ (proj₁ ΓΣ) (proj₁ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ)) (proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) ((Con-∃-▷ ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ)))))) ⟩
        πᴰ (proj₁ ΓΣ) (proj₁ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ)) (proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) ((Con-∃-▷ ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ)))))
          ≡⟨ ≡.dcong₂ (πᴰ (proj₁ ΓΣ)) r s ⟩
        --   ≡⟨ ≡.cong₂ {!πᴰ (proj₁ ΓΣ)!} pA {!≡.trans (Ty-∃-irrel (proj₁ B) (proj₂ B) _ _ _) pB!} ⟩
        πᴰ (proj₁ ΓΣ) (proj₁ AΣ) (proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B)
          (Con-∃-▷ ΓΣ _))) ∎
        where
        open ≡.≡-Reasoning
        r : proj₁ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ)
          ≡ subst (λ ○ → Tyᴰ ○ A) (Con-∃!-rec Γ₀ Γ₁ ΓΣ) (proj₁ (Ty-∃ A))
        r = ≡.sym (Ty-∃-irrel (proj₁ A) (proj₂ A) (Con-∃ (Γ₀ , Γ₁)) ΓΣ (Con-∃!-rec Γ₀ Γ₁ ΓΣ))
        s : subst (λ z → Tyᴰ (proj₁ ΓΣ ▷ᴰ z) B) r (proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ))))
          ≡ proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ (trans-ElimTyΣ ΓΣ ΓΣ ≡.refl (subst (λ ○ → Tyᴰ ○ A) (Con-∃!-rec Γ₀ Γ₁ ΓΣ) (proj₁ (Ty-∃ A)) , _))))
        s =
          subst (λ z → Tyᴰ (proj₁ ΓΣ ▷ᴰ z) B) r (proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ (Ty-∃-rec (proj₁ A) (proj₂ A) ΓΣ))))
            ≡⟨ {!!} ⟩
          proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ (trans-ElimTyΣ ΓΣ ΓΣ ≡.refl (subst (λ ○ → Tyᴰ ○ A) (Con-∃!-rec Γ₀ Γ₁ ΓΣ) (proj₁ (Ty-∃ A)) , _))))
            ≡⟨ {!!} ⟩
          proj₁ (Ty-∃-rec (proj₁ B) (proj₂ B) (Con-∃-▷ ΓΣ (trans-ElimTyΣ ΓΣ ΓΣ ≡.refl (subst (λ ○ → Tyᴰ ○ A) (Con-∃!-rec Γ₀ Γ₁ ΓΣ) (proj₁ (Ty-∃ A)) , _)))) ∎
