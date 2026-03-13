module QIT.KKA2019.Syntax where

open import QIT.Prelude hiding (_,_)

module _ {ℓ : Level} where
  -- Sketch of codes
  interleaved mutual
    data Con : Set (lsuc ℓ)
    data Sub : Con → Con → Set (lsuc ℓ)
    data Ty : Con → Set (lsuc ℓ)
    -- data _≈ᵀ_ : ∀ {Γ} → Ty Γ → Ty Γ → Prop (lsuc ℓ)
    data Tm : (Γ : Con) → Ty Γ → Set (lsuc ℓ)
    data _≈ᵗ_ : ∀ {Γ} {A B : Ty Γ} → Tm Γ A → Tm Γ B → Prop (lsuc ℓ)

    data _ where
      ∙ : Con
      _▷_ : ∀ Γ → Ty Γ → Con
      U : ∀ {Γ} → Ty Γ
      El : ∀ {Γ A} → Tm Γ A → Ty Γ
      Id : ∀ {Γ} → (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ
      _[_]ᵀ : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ 
      ε : ∀ {Γ} → Sub Γ ∙
      id : ∀ {Γ} → Sub Γ Γ
      _∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ 
      _,_ : ∀ {Γ Δ A}
          → (σ : Sub Γ Δ)
          → Tm Γ (A [ σ ]ᵀ)
          → Sub Γ (Δ ▷ A)
      _[_]ᵗ : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ᵀ)
      π₁ : ∀ {Γ Δ A} → Sub Γ (Δ ▷ A) → Sub Γ Δ
      π₂ : ∀ {Γ Δ A} → (σ : Sub Γ (Δ ▷ A)) → Tm Γ (A [ π₁ σ ]ᵀ)
      Π̂ : ∀ {Γ} → (a : Tm Γ U) → Ty (Γ ▷ El a) → Ty Γ
      λ̂ : ∀ {Γ} → (a : Tm Γ U) → {B : Ty (Γ ▷ El a)} → (t : Tm (Γ ▷ El a) B) → Tm Γ (Π̂ a B)
      _﹫ʳ_ : ∀ {Γ a} {B : Ty (Γ ▷ El a)} → (f : Tm Γ (Π̂ a B)) → (t : Tm Γ (El a)) → Tm Γ (B [ id , (t [ id ]ᵗ) ]ᵀ)

      -- Equations
      β-red : ∀ {Γ} → (a : Tm Γ U) → {B : Ty (Γ ▷ El a)} → (t : Tm (Γ ▷ El a) B) → (u : Tm Γ (El a))
            → ((λ̂ a t) ﹫ʳ u) ≈ᵗ (t [ id , (u [ id ]ᵗ) ]ᵗ)
      ≈t-refl : ∀ {Γ} {A : Ty Γ} → (t : Tm Γ A) → t ≈ᵗ t
      ≈t-sym : ∀ {Γ} {A B : Ty Γ} → (t : Tm Γ A) (u : Tm Γ B) → t ≈ᵗ u → u ≈ᵗ t
      ≈t-trans : ∀ {Γ} {A B C : Ty Γ} → (s : Tm Γ A) (t : Tm Γ B) (u : Tm Γ C) → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u
