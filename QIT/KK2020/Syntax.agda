module QIT.KK2020.Syntax where

open import QIT.Prelude
open import QIT.KK2020.Level

module _ {ℓ : Level} where
  data Con : Set (lsuc ℓ)
  data Sub : Con → Con → Set (lsuc ℓ)
  data Ty : Con → Set (lsuc ℓ)
  data Tm : (Γ : Con) → Ty Γ → Set (lsuc ℓ)

  data Con where
    ∙ : Con
    _▷_ : ∀ Γ → Ty Γ → Con

  _[_]ᵀ : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ 
  _[_]ᵗ : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ᵀ)
    
  data Sub where
    ε : ∀ {Γ} → Sub Γ ∙
    id : ∀ {Γ} → Sub Γ Γ
    _∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ 
    _,_ : ∀ {Γ Δ A}
        → (σ : Sub Γ Δ)
        → Tm Γ (A [ σ ]ᵀ)
        → Sub Γ (Δ ▷ A)
    π₁ : ∀ {Γ Δ A} → Sub Γ (Δ ▷ A) → Sub Γ Δ

  data Ty where
    U : ∀ {Γ} → Ty Γ
    El : ∀ {Γ A} → Tm Γ A → Ty Γ
    Πʳ : ∀ {Γ} → (a : Tm Γ U) → Ty (Γ ▷ El a) → Ty Γ
    Πᵉ : ∀ {Γ} → (X : Set ℓ) → (X → Ty Γ) → Ty Γ
    Id : ∀ {Γ} → (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ

  data Tm where
    _＠ʳ_ : ∀ {Γ a} → Tm Γ (Πʳ a U) → Tm Γ (El a) → Tm Γ U
    _＠ᵉ_ : ∀ {Γ} {X : Set ℓ} {Â : X → Ty Γ}
         → (t : Tm Γ (Πᵉ X Â)) → (x : X) → Tm Γ (Â x)
    π₂ : ∀ {Γ Δ A} → (σ : Sub Γ (Δ ▷ A)) → Tm Γ (A [ π₁ σ ]ᵀ)

  wk : ∀ {Γ A} → Sub (Γ ▷ A) Γ
  wk = π₁ id
  vz = π₂ id

  U [ σ ]ᵀ = U
  El a [ σ ]ᵀ = El (a [ σ ]ᵗ)
  Πʳ a A [ σ ]ᵀ = Πʳ (a [ σ ]ᵗ) (A [ (σ ∘ π₁ id) , {!!} ]ᵀ)
  Πᵉ X x [ σ ]ᵀ = {!!}
  Id A x x₁ [ σ ]ᵀ = {!!}
