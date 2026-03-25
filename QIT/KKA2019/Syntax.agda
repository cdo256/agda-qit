open import QIT.Prelude hiding (_,_)

module QIT.KKA2019.Syntax where

interleaved mutual
  infix 10 _≈ᵀ_ _≈ᵗ_ _≈ˢ_
  infixl 15 _▷_
  infixl 25 _[_]ᵀ _[_]ᵗ
  infixr 30 _,_ 
  infixr 30 _∘_ 
  data Con : Set
  data Sub : Con → Con → Set
  data _≈ˢ_ : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set
  data Ty : Con → Set
  data _≈ᵀ_ : ∀ {Γ} → Ty Γ → Ty Γ → Prop
  data Tm : (Γ : Con) → Ty Γ → Set
  data _≈ᵗ_ : ∀ {Γ} {A B : Ty Γ} → Tm Γ A → Tm Γ B → Prop

  variable
    Γ Δ Θ Ξ : Con
    A B C : Ty Γ
    σ : Sub Γ Δ

  -- Substitution Calculus
  data _ where
    ∙ : Con
    _▷_ : ∀ Γ → Ty Γ → Con
    _[_]ᵀ : Ty Δ → Sub Γ Δ → Ty Γ 
    id : Sub Γ Γ
    _∘_ : Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
    ε : Sub Γ ∙
    _,_ : (σ : Sub Γ Δ)
        → Tm Γ (A [ σ ]ᵀ)
        → Sub Γ (Δ ▷ A)
    π₁ : Sub Γ (Δ ▷ A) → Sub Γ Δ
    π₂ : (σ : Sub Γ (Δ ▷ A)) → Tm Γ (A [ π₁ σ ]ᵀ)
    _[_]ᵗ : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ᵀ)
    [id] : (A : Ty Γ) → A [ id ]ᵀ ≈ᵀ A
    [∘] : (A : Ty Θ) (σ : Sub Γ Θ) (δ : Sub Δ Γ) → A [ σ ∘ δ ]ᵀ ≈ᵀ A [ σ ]ᵀ [ δ ]ᵀ
    ass : (ν : Sub Θ Ξ) (σ : Sub Γ Θ) (δ : Sub Δ Γ) → ν ∘ (σ ∘ δ) ≈ˢ (ν ∘ σ) ∘ δ
    idl : (σ : Sub Γ Δ) → id ∘ σ ≈ˢ σ
    idr : (σ : Sub Γ Δ) → σ ∘ id ≈ˢ σ


  wk : Sub (Γ ▷ A) Γ
  wk = π₁ id
  vz : Tm (Γ ▷ A) (A [ wk ]ᵀ)
  vz = π₂ id
  vs : (t : Tm Γ A) → Tm (Γ ▷ B) (A [ wk ]ᵀ)
  vs t = t [ wk ]ᵗ
  ⟨_⟩ : Tm Γ A → Sub Γ (Γ ▷ A)
  ⟨ t ⟩ = id , (t [ id ]ᵗ)
  _↑ : (σ : Sub Γ Δ) → Sub (Γ ▷ A [ σ ]ᵀ) (Δ ▷ A)
  _↑ {Γ} {A = A} σ = (σ ∘ wk) , coe (≈T-sym ([∘] A σ wk)) vz

  -- Types
  data _ where
    U : ∀ {Γ} → Ty Γ
    El : Tm Γ A → Ty Γ
    U[] : (σ : Sub Γ Δ) → U [ σ ]ᵀ ≈ᵀ U
    El[] : (σ : Sub Γ Δ) (a : Tm Δ U) → El a [ σ ]ᵀ ≈ᵀ El (a [ σ ]ᵗ) 

    Πⁱ : (a : Tm Γ U) → Ty (Γ ▷ El a) → Ty Γ
    λⁱ : (a : Tm Γ U) → {B : Ty (Γ ▷ El a)} → (t : Tm (Γ ▷ El a) B) → Tm Γ (Πⁱ a B)
    _﹫ⁱ_ : ∀ {Γ a} {B : Ty (Γ ▷ El a)} → (f : Tm Γ (Πⁱ a B)) → (t : Tm Γ (El a)) → Tm Γ (B [ id , (t [ id ]ᵗ) ]ᵀ)
    Πⁱ[] : ∀ {Γ} → (a : Tm Γ U) → Ty (Γ ▷ El a) → Ty Γ 
    -- TODO
    -- ηΠⁱ : ∀ {Γ} → (a : Tm Γ U) (b : Tm (Γ ▷ El a) U) → {B : Ty (Γ ▷ El a)} → (t : Tm {!!} {!!}) → (u : Tm (Γ ▷ El a) (El b))
    --     → (λⁱ a ({!vs t [ ? ]ᵗ!} ﹫ⁱ {!vz!})) ≈ᵗ {!t [ id , {!!} ]ᵗ!}
    βΠ : ∀ {Γ} → (a : Tm Γ U) → {B : Ty (Γ ▷ El a)} → (t : Tm (Γ ▷ El a) B) → (u : Tm Γ (El a))
        → ((λⁱ a t) ﹫ⁱ u) ≈ᵗ (t [ id , (u [ id ]ᵗ) ]ᵗ)
    Id : ∀ {Γ} → (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ

    -- Structural Equations
    ≈T-refl : A ≈ᵀ A
    ≈T-sym : A ≈ᵀ B → B ≈ᵀ A
    ≈T-trans : A ≈ᵀ B → B ≈ᵀ C → A ≈ᵀ C
    ≈t-refl : (t : Tm Γ A) → t ≈ᵗ t
    ≈t-sym : (t : Tm Γ A) (u : Tm Γ B) → t ≈ᵗ u → u ≈ᵗ t
    ≈t-trans : (s : Tm Γ A) (t : Tm Γ B) (u : Tm Γ C) → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u
    coe : A ≈ᵀ B → Tm Γ A → Tm Γ B
    reflect : ∀ {Γ A} → (s t : Tm Γ A) → (w : Tm Γ (Id A s t)) → s ≈ᵗ t

record Code : Set₁ where
  field
    Con₀ : Set
    Ty₀ : Con₀ → Set
    Sub₀ : Con₀ → Con₀ → Set
    Tm₀ : (Γ : Con₀) → Ty₀ Γ → Set
    
record Algebra : Set₂ where
  field
    Conᴬ : Con → Set₁
    Tyᴬ : Ty Γ → (Conᴬ Γ) → Set₁
    Subᴬ : Sub Γ Δ → Conᴬ Γ → Conᴬ Δ
    Tmᴬ : Tm Γ A → (Γ̇ : Conᴬ Γ) → Tyᴬ A Γ̇

open Algebra
  
-- Cons : (Ω : Con) (ν : Sub Ω Γ) → Algebra
-- Cons Ω ν .Conᴬ ∙ = ⊤*
-- Cons Ω ν .Conᴬ (Γ ▷ A) = Σ (Cons Ω ν .Conᴬ Γ) λ Γ̇ → Cons Ω ν .Conᴬ Γ
-- Cons Ω ν .Tyᴬ U Γ̇ = {!Tm Ω {!El ?!}!}
-- Cons Ω ν .Tyᴬ {Γ} (El a) Γ̇ = let w = Cons Ω ν .Tmᴬ a Γ̇ in {!!}
-- Cons Ω ν .Tyᴬ (Πⁱ a B) Γ̇ = {!!}
-- Cons Ω ν .Tyᴬ (A [ σ ]ᵀ) Γ̇ = {!!}
-- Cons Ω ν .Tyᴬ (Πⁱ[] a A) Γ̇ = {!!}
-- Cons Ω ν .Tyᴬ (Id A x x₁) Γ̇ = {!!}
-- Cons {Γ = Γ} Ω ν .Subᴬ {Γ = Γ'} {Δ} σ Γᴬ = let w = Cons Ω ({!!} ∘ ν) .Conᴬ {!!} in {!!}
-- Cons Ω ν .Tmᴬ = {!!}
-- --   field
-- --     Conᴬ : (Γ : Con) → Conᴬ {!!} {!!}
-- -- --     Tyᴬ : Ty Γ → (Conᴬ Γ) → Set
-- -- --     Subᴬ : Sub Γ Δ → Conᴬ Γ → Conᴬ Δ
-- -- --     Tmᴬ : Tm Γ A → (Γ̇ : Conᴬ Γ) → Tyᴬ A Γ̇

-- -- -- module Nat where
-- -- --   sig : Con
-- -- --   sig =
-- -- --     ∙ ▷ U -- N
-- -- --       ▷ El vz -- z
-- -- --       ▷ Πⁱ (coe (U[] wk) vz) (El (vs vz)) [ wk ]ᵀ -- s
