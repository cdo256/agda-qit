module QIT.KK2020.Syntax where

open import QIT.Prelude
open import QIT.KK2020.Level

module _ {ℓ : Level} where
  data Con : Set (lsuc ℓ)
  data Sub : Con → Con → Set (lsuc ℓ)
  data Ty : Con → Set (lsuc ℓ)
  data Tm : (Γ : Con) → Ty Γ → Set (lsuc ℓ)

  postulate
    El : ∀ {Γ A} → Tm Γ A → Ty Γ

  _[_]ᵀ : ∀ {Γ Δ} → Ty Γ → Sub Γ Δ → Ty Δ
  _[_]ᵗ : ∀ {Γ Δ} → {A : Ty Γ} → Tm Γ A → (σ : Sub Γ Δ) → Tm Δ (A [ σ ]ᵀ)

  data Con where
    ∙ : Con
    _▷_ : ∀ Γ → Ty Γ → Con
    
  data Sub where
    ε : ∀ {Γ} → Sub Γ ∙
    id : ∀ {Γ} → Sub Γ Γ
    _∘_ : ∀ {Γ Δ Ξ} → Sub Γ Δ → Sub Δ Ξ → Sub Γ Ξ 

  data Ty where
    U : ∀ {Γ} → Ty Γ
    Πʳ : ∀ {Γ} → (a : Tm Γ U) → Ty (Γ ▷ El a) → Ty Γ
    Πᵉ : ∀ {Γ} → (X : Set ℓ) → (X → Ty Γ) → Ty Γ
    _＠ᵉ_ : ∀ {Γ} → {X : Set ℓ} {Â : X → Ty Γ} → {!!} → X → Ty Γ
    Id : ∀ {Γ} → (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ

  U [ σ ]ᵀ = U
  Πʳ a A [ σ ]ᵀ = Πʳ (a [ σ ]ᵗ) (A [ {!!} ]ᵀ)
  Πᵉ X Â [ σ ]ᵀ = Πᵉ X λ x → Â x [ σ ]ᵀ
  (Â ＠ᵉ x) [ σ ]ᵀ = {!λ x → Â x [ ? ]ᵀ!} ＠ᵉ {!!}
  Id A x x₁ [ σ ]ᵀ = {!!}

  data Tm where
    Πⁱ : ∀ {Γ} {X : Set ℓ} → (X → Tm Γ U) → Tm Γ U
    _＠ʳ_ : ∀ {Γ a} → Tm Γ (Πʳ a U) → Tm Γ (El a) → Tm Γ U
    _＠ⁱ_ : ∀ {Γ} {X : Set ℓ} {â : X → Tm Γ U} → Tm Γ (El (Πⁱ â)) → X → Tm Γ U
    _＠ᵉ_ : ∀ {Γ} {X : Set ℓ} {Â : X → Ty Γ}
         → (t : Tm Γ (Πᵉ X Â)) → (x : X) → Tm Γ (Â x)
