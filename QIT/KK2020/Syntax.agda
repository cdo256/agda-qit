module QIT.KK2020.Syntax where

open import QIT.Prelude hiding (_,_)
open import QIT.KK2020.Level

module _ {ℓ : Level} where
  infixl 5 _▷_
  infixl 6 _,_
  infixr 7 _⇒_
  infixr 7 _⇒ᵉ_
  infixl 8 _[_]Ty
  infixl 8 _[_]Tm
  infixl 9 _∘_

  postulate
    Con : Set (lsuc ℓ)
    Ty : Con → Set (lsuc ℓ)
    Sub : Con → Con → Set (lsuc ℓ)
    Tm : (Γ : Con) → Ty Γ → Set (lsuc ℓ)

  postulate
    _[_]Ty : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    _[_]Tm : ∀ {Γ Δ} → {A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]Ty)

  postulate
    ∙   : Con
    _▷_ : (Γ : Con) → Ty Γ → Con

  postulate
    U   : ∀ {Γ} → Ty Γ
    El  : ∀ {Γ} → Tm Γ U → Ty Γ
    Πʳ  : ∀ {Γ}
        → (a : Tm Γ U)
        → Ty (Γ ▷ El a)
        → Ty Γ
    Πᵉ  : ∀ {Γ}
        → (X : Set ℓ)
        → (X → Ty Γ)
        → Ty Γ
    Id  : ∀ {Γ}
        → (a : Tm Γ U)
        → Tm Γ (El a)
        → Tm Γ (El a)
        → Ty Γ

  postulate
    ε   : ∀ {Γ} → Sub Γ ∙
    id  : ∀ {Γ} → Sub Γ Γ
    _∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
    _,_ : ∀ {Γ Δ}
        → {A : Ty Δ}
        → (σ : Sub Γ Δ)
        → Tm Γ (A [ σ ]Ty)
        → Sub Γ (Δ ▷ A)

  postulate
    appʳ : ∀ {Γ}
          → {a : Tm Γ U}
          → {B : Ty (Γ ▷ El a)}
          → Tm Γ (Πʳ a B)
          → Tm (Γ ▷ El a) B

    appᵉ : ∀ {Γ}
          → {X : Set ℓ}
          → {B : X → Ty Γ}
          → Tm Γ (Πᵉ X B)
          → (x : X)
          → Tm Γ (B x)

  postulate
    _↑_ : ∀ {Γ Δ}
        → (σ : Sub Γ Δ)
        → (a : Tm Δ U)
        → Sub (Γ ▷ El (a [ σ ]Tm)) (Δ ▷ El a)
    π₁ : ∀ {Γ Δ} → {A : Ty Δ} → Sub Γ (Δ ▷ A) → Sub Γ Δ

  postulate
    U[] : ∀ {σ} → U [ σ ]Ty ≡ U
    El[] : ∀ {σ a} → El a [ σ ]Ty ≡ El (a [ σ ]Tm)
    Πʳ[] : ∀ {σ a B} → Πʳ a B [ σ ]Ty ≡ Πʳ (a [ σ ]Tm) (B [ σ ↑ a ]Ty)
    Πᵉ[] : ∀ {σ X B} → Πᵉ X B [ σ ]Ty ≡ Πᵉ X (λ x → B x [ σ ]Ty)
    Id[] : ∀ {σ a t u} → Id a t u [ σ ]Ty ≡ Id (a [ σ ]Tm) (t [ σ ]Tm) (u [ σ ]Tm)

  postulate
    ↑₁ : ∀ {σ a} → σ ↑ a ≡ {!(σ ∘ wk) , vz!}

  postulate
    appʳ[] : ∀ {σ t} → appʳ t [ σ ]Tm ≡ appʳ (t [ σ ]Tm)
    appᵉ[] : ∀ {σ t x} → appᵉ t x [ σ ]Tm ≡ appᵉ (t [ σ ]Tm) x

  postulate
    π₁≡ : ∀ {σ t} → π₁ (σ , t) ≡ σ

  postulate
    π₂ : ∀ {Γ Δ} → {A : Ty Δ} → (σ : Sub Γ (Δ ▷ A)) → Tm Γ (A [ π₁ σ ]Ty)

  wk : ∀ {Γ} {A : Ty Γ} → Sub (Γ ▷ A) Γ
  wk = π₁ id

  vz : ∀ {Γ} {A : Ty Γ} → Tm (Γ ▷ A) (A [ wk ]Ty)
  vz = π₂ id

  vs : ∀ {Γ}
    → {A B : Ty Γ}
    → Tm Γ A
    → Tm (Γ ▷ B) (A [ wk ]Ty)
  vs t = t [ wk ]Tm

  ⟨_⟩ : ∀ {Γ} {A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▷ A)
  ⟨ t ⟩ = id , t

  _⇒_ : ∀ {Γ} → Tm Γ U → Ty Γ → Ty Γ
  a ⇒ B = Πʳ a (B [ wk ]Ty)

  _⇒ᵉ_ : ∀ {Γ} → Set ℓ → Ty Γ → Ty Γ
  X ⇒ᵉ B = Πᵉ X (λ _ → B)

  _＠ʳ_ : ∀ {Γ}
      → {a : Tm Γ U}
      → {B : Ty (Γ ▷ El a)}
      → (t : Tm Γ (Πʳ a B))
      → (u : Tm Γ (El a))
      → Tm Γ (B [ ⟨ u ⟩ ]Ty)
  t ＠ʳ u = appʳ t [ ⟨ u ⟩ ]Tm

  _＠_ : ∀ {Γ}
      → {a : Tm Γ U}
      → {B : Ty Γ}
      → Tm Γ (a ⇒ B)
      → Tm Γ (El a)
      → Tm Γ B
  t ＠ u = t ＠ʳ u
