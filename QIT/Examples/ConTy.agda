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

    ElimTyΣ≡ : {Γ : Con} {A : Ty Γ} {ΓΣ ΓΣ' : ElimConΣ Γ} (p : ElimConΣ≡ ΓΣ ΓΣ') → {AΣ : ElimTyΣ A ΓΣ} {AΣ' : ElimTyΣ A ΓΣ'} → Set
    ElimTyΣ≡ {ΓΣ = Γ̂ , _} {ΓΣ' = Γ̂' , _} ≡.refl = Γ̂ ≡ Γ̂'

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
      Con-∃-▷ : (Γ : Con) (ΓΣ : ElimConΣ Γ)
              → (A : Ty Γ) (AΣ : ElimTyΣ A ΓΣ)
              → ElimConΣ (Γ ▷ A)
      Con-∃-▷ Γ (Γ̂ , Γᵉ) A (Â , Aᵉ) =
        (Γ̂ ▷ᴰ Â) , e▷ Γᵉ Aᵉ

      Ty-∃-ι : {Γ₀ : Con₀} (Γ₁ Γ₁' : Con₁ Γ₀) (pΓ₁ : Γ₁ ≡ Γ₁') (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
             → ElimTyΣ (ι (Γ₀ , Γ₁')) ΓΣ
      Ty-∃-ι {Γ₀} Γ₁ .Γ₁ ≡.refl (Γ̂ , Γᵉ) = ιᴰ Γ̂ , eι Γᵉ

      Ty-∃-π : {Γ₀ : Con₀} (Γ₁ Γ₁' : Con₁ Γ₀) (pΓ₁ : Γ₁ ≡ Γ₁') (ΓΣ : ElimConΣ (Γ₀ , Γ₁))
             → (A : Ty (Γ₀ , Γ₁)) (AΣ : ElimTyΣ A ΓΣ)
             → (ΔΣ : ElimConΣ ((Γ₀ , Γ₁) ▷ A))
             → (B : Ty ((Γ₀ , Γ₁) ▷ A)) (BΣ : ElimTyΣ B (Con-∃-▷ (Γ₀ , Γ₁) ΓΣ A AΣ))
             → ElimTyΣ (π (Γ₀ , Γ₁') A B) ΓΣ
      Ty-∃-π Γ₁ .Γ₁ ≡.refl (Γ̂ , Γᵉ) A (Â , Aᵉ) (Δ̂ , Δᵉ) B (B̂ , Bᵉ) =
             πᴰ Γ̂ Â B̂ , eπ Γᵉ Aᵉ (e▷ Γᵉ Aᵉ) Bᵉ
             
      Con-∃-rec : (Γ₀ : Con₀) (Γ₁ : Con₁ Γ₀)
                → ElimConΣ (Γ₀ , Γ₁)
      Con-∃-rec ∙₀ ∙₁ =
        Con-∃-∙
      Con-∃-rec (Γ₀ ▷₀ A₀) (Γ₁ ▷₁ A₁) =
        Con-∃-▷ (Γ₀ , Γ₁) (Con-∃-rec Γ₀ Γ₁) (A₀ , A₁) (Ty-∃-rec A₀ A₁ (Con-∃-rec Γ₀ Γ₁))

      Ty-∃-rec : {Γ₀ : Con₀} {Γ₁ : Con₁ Γ₀} (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀)
               → (ΓΣ : ElimConΣ (Γ₀ , Γ₁)) → ElimTyΣ (A₀ , A₁) ΓΣ
      Ty-∃-rec {Γ₀} {Γ₁} (ι₀ Γ₀) (ι₁ Γ₁') (Γ̂ , Γᵉ) =
        Ty-∃-ι Γ₁ Γ₁' (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ)
      Ty-∃-rec {Γ₀} {Γ₁} (π₀ Γ₀ A₀ B₀) (π₁ Γ₁' A₁ B₁) (Γ̂ , Γᵉ) =
        Ty-∃-π Γ₁ Γ₁' (isPropCon₁ Γ₁ Γ₁') (Γ̂ , Γᵉ)
               (A₀ , A₁) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ))
               (Con-∃-rec (Γ₀ ▷₀ A₀) (Γ₁ ▷₁ A₁))
               (B₀ , B₁) (Ty-∃-rec B₀ B₁ (Con-∃-▷ (Γ₀ , Γ₁) (Γ̂ , Γᵉ) (A₀ , A₁) (Ty-∃-rec A₀ A₁ (Γ̂ , Γᵉ))))


    --   Ty-∃ : {Γ₀ : Con₀} {Γ₁ : Con₁ Γ₀} (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀)
    --         → (Γ̂ : Conᴰ (Γ₀ , Γ₁)) → ElimCon (Γ₀ , Γ₁) Γ̂ → Σ (Tyᴰ Γ̂ (A₀ , A₁)) (ElimTy Γ̂ (A₀ , A₁) )
    --   Ty-∃ {Γ₀} {Γ₁} (ι₀ Γ₀) (ι₁ Γ₁') Γ̂ Γᵉ with isPropCon₁ Γ₁' Γ₁
    --   ... | ≡.refl = ιᴰ Γ̂ , eι Γᵉ
    --   Ty-∃ {Γ₀} {Γ₁} (π₀ Γ₀ A₀ B₀) (π₁ Γ₁' A₁ B₁) Γ̂ Γᵉ with isPropCon₁ Γ₁' Γ₁
    --   ... | ≡.refl =
    --     let (Â , Aᵉ) = Ty-∃ A₀ A₁ Γ̂ Γᵉ
    --         (B̂ , Bᵉ) = Ty-∃ B₀ B₁ (Γ̂ ▷ᴰ Â) (e▷ Γᵉ Aᵉ)
    --     in πᴰ Γ̂ Â B̂ , eπ Γᵉ Aᵉ (e▷ Γᵉ Aᵉ) Bᵉ

    -- -- mutual
    -- --   Con-∃ : (Γ₀ : Con₀) (Γ₁ : Con₁ Γ₀) → Σ (Conᴰ (Γ₀ , Γ₁)) (ElimCon (Γ₀ , Γ₁))
    -- --   Con-∃ ∙₀ ∙₁ = ∙ᴰ , e∙
    -- --   Con-∃ (Γ₀ ▷₀ A₀) (Γ₁ ▷₁ A₁) =
    -- --     let (Γ̂ , Γᵉ) = Con-∃ Γ₀ Γ₁
    -- --         (Â , Aᵉ) = Ty-∃ A₀ A₁ Γ̂ Γᵉ
    -- --     in (Γ̂ ▷ᴰ Â) , e▷ Γᵉ Aᵉ

    -- --   Ty-∃ : {Γ₀ : Con₀} {Γ₁ : Con₁ Γ₀} (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀)
    -- --         → (Γ̂ : Conᴰ (Γ₀ , Γ₁)) → ElimCon (Γ₀ , Γ₁) Γ̂ → Σ (Tyᴰ Γ̂ (A₀ , A₁)) (ElimTy Γ̂ (A₀ , A₁) )
    -- --   Ty-∃ {Γ₀} {Γ₁} (ι₀ Γ₀) (ι₁ Γ₁') Γ̂ Γᵉ with isPropCon₁ Γ₁' Γ₁
    -- --   ... | ≡.refl = ιᴰ Γ̂ , eι Γᵉ
    -- --   Ty-∃ {Γ₀} {Γ₁} (π₀ Γ₀ A₀ B₀) (π₁ Γ₁' A₁ B₁) Γ̂ Γᵉ with isPropCon₁ Γ₁' Γ₁
    -- --   ... | ≡.refl =
    -- --     let (Â , Aᵉ) = Ty-∃ A₀ A₁ Γ̂ Γᵉ
    -- --         (B̂ , Bᵉ) = Ty-∃ B₀ B₁ (Γ̂ ▷ᴰ Â) (e▷ Γᵉ Aᵉ)
    -- --     in πᴰ Γ̂ Â B̂ , eπ Γᵉ Aᵉ (e▷ Γᵉ Aᵉ) Bᵉ

    -- -- Ty-∃-irrel : ∀ {Γ₀ Γ₁ Γ̂} (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀) (Γᵉ Γᵉ' : ElimCon (Γ₀ , Γ₁) Γ̂)
    -- --           → proj₁ (Ty-∃ A₀ A₁ Γ̂ Γᵉ) ≡ proj₁ (Ty-∃ A₀ A₁ Γ̂ Γᵉ')
    -- -- Ty-∃-irrel {Γ̂ = Γ̂} (π₀ ._ A₀ B₀) (π₁ Γ₁' A₁ B₁) Γᵉ Γᵉ' 
    -- --   with isPropCon₁ Γ₁' _ 
    -- -- ... | ≡.refl = helper (Ty-∃ A₀ A₁ Γ̂ Γᵉ) (Ty-∃ A₀ A₁ Γ̂ Γᵉ') (Ty-∃-irrel A₀ A₁ Γᵉ Γᵉ')
    -- --   where
    -- --     helper : (resA resA' : Σ _ _) → (p : proj₁ resA ≡ proj₁ resA') → _
    -- --     helper resA resA' ≡.refl = ≡.cong (πᴰ _ (proj₁ resA)) (Ty-∃-irrel B₀ B₁ _ _)

    -- -- mutual
    -- --   Con-∃! : (Γ₀ : Con₀) (Γ₁ : Con₁ Γ₀) → ∀ Γ̂ → ElimCon (Γ₀ , Γ₁) Γ̂ → proj₁ (Con-∃ Γ₀ Γ₁) ≡ Γ̂
    -- --   Con-∃! ∙₀ ∙₁ Γ̂ e∙ = ≡.refl
    -- --   Con-∃! (Γ₀ ▷₀ A₀) (Γ₁ ▷₁ A₁) Δ̂ (e▷ {Γ̂ = Γ̂} {Â = Â} Γᵉ Aᵉ)
    -- --     with Con-∃! Γ₀ Γ₁ Γ̂ Γᵉ | Ty-∃! A₀ A₁ Γ̂ Γᵉ Â Aᵉ
    -- --   ... | ≡.refl | ≡.refl =
    -- --     let (Γ̂' , Γᵉ') = Con-∃ Γ₀ Γ₁
    -- --         (Â' , Aᵉ') = Ty-∃ A₀ A₁ Γ̂' Γᵉ'
    -- --         in ≡.cong (Γ̂' ▷ᴰ_) (≡.sym (Ty-∃! A₀ A₁ Γ̂' Γᵉ Â' Aᵉ'))

    -- --   Ty-∃! : {Γ₀ : Con₀} {Γ₁ : Con₁ Γ₀} (A₀ : Ty₀) (A₁ : Ty₁ Γ₀ A₀)
    -- --         → (Γ̂ : Conᴰ (Γ₀ , Γ₁)) → (Γᵉ : ElimCon (Γ₀ , Γ₁) Γ̂) 
    -- --         → (Â : Tyᴰ Γ̂ (A₀ , A₁)) (Aᵉ : ElimTy Γ̂ (A₀ , A₁) Â)
    -- --         → proj₁ (Ty-∃ A₀ A₁ Γ̂ Γᵉ) ≡ Â
    -- --   Ty-∃! {Γ₀} {Γ₁} (ι₀ .Γ₀) (ι₁ Γ₁') Γ̂ Γᵉ _ (eι _) with isPropCon₁ Γ₁' Γ₁
    -- --   ... | ≡.refl = ≡.refl
    -- --   Ty-∃! {Γ₀} {Γ₁} (π₀ Γ₀ A₀ B₀) (π₁ Γ₁' A₁ B₁) Γ̂ Γᵉ _ (eπ Γᵉ' Aᵉ Δᵉ Bᵉ) with isPropCon₁ Γ₁' Γ₁
    -- --   ... | ≡.refl with Ty-∃! A₀ A₁ Γ̂ Γᵉ _ Aᵉ
    -- --   ... | ≡.refl with Ty-∃! B₀ B₁ (Γ̂ ▷ᴰ _) Δᵉ _ Bᵉ
    -- --   ... | ≡.refl = {!!}
