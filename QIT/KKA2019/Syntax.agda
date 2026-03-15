open import QIT.Prelude hiding (_,_)

module QIT.KKA2019.Syntax {ℓ : Level} where

interleaved mutual
  infix 10 _≈ᵀ_ _≈ᵗ_ _≈ˢ_
  infixl 15 _▷_
  infixl 25 _[_]ᵀ _[_]ᵗ
  infixr 30 _,_ 
  infixr 30 _∘_ 
  data Con : Set (lsuc ℓ)
  data Sub : Con → Con → Set (lsuc ℓ)
  data _≈ˢ_ : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set (lsuc ℓ)
  data Ty : Con → Set (lsuc ℓ)
  data _≈ᵀ_ : ∀ {Γ} → Ty Γ → Ty Γ → Prop (lsuc ℓ)
  data Tm : (Γ : Con) → Ty Γ → Set (lsuc ℓ)
  data _≈ᵗ_ : ∀ {Γ} {A B : Ty Γ} → Tm Γ A → Tm Γ B → Prop (lsuc ℓ)

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

module Example1 where
  ΠAA : (a : Tm Γ U) → Ty Γ
  ΠAA a = Πⁱ a (El a [ wk ]ᵀ)
  I : (a : Tm Γ U) → Tm Γ (ΠAA a)
  I a = λⁱ a vz
  K : (a : Tm Γ U) (b : Tm Γ U) → Tm Γ (Πⁱ a (Πⁱ (coe (U[] wk) (b [ wk ]ᵗ)) (El a [ π₁ wk ]ᵀ)))
  K a b = λⁱ a (λⁱ (coe _ (b [ wk ]ᵗ)) (π₂ wk))

module Monad where
  open import Effect.Monad

  record Theory : Set (lsuc ℓ) where
    constructor theory
    field
      ctx : Con

  -- The 'Effect' of extending a theory with a type (a Sort)
  extend-T : (T : Theory) → (Ty (Theory.ctx T)) → Theory
  extend-T (theory Γ) A = theory (Γ ▷ A)

  -- The 'Effect' of extending a theory with a term (a Constructor)
  -- This is technically the same operation on the context level
  extend-t : (T : Theory) → (A : Ty (Theory.ctx T)) → Tm (Theory.ctx T) A → Theory
  extend-t (theory Γ) A t = theory (Γ ▷ Id A (coe ≈T-refl t) (coe ≈T-refl t))

  infixl 1 _▹_ _►_

  _▹_ : (T : Theory) → (∀ {Γ} → (Tm Γ U) → Theory) → Theory
  theory Γ ▹ f = f {Γ ▷ U} (coe (U[] wk) vz)

  _►_ : (T : Theory)
      → (A : Ty (Theory.ctx T))
      → (∀ {Γ} → (Tm Γ (A [ {!!} ]ᵀ)) → Theory) → Theory
  (theory Γ ► A) f = f {Γ ▷ A} {!vz!}

module Syntax where
  open import Effect.Monad

  record Theory : Set (lsuc ℓ) where
    constructor theory
    field
      ctx : Con

  infixl 1 ▹_ _►_

--   ▹_ : (∀ (T : Theory) → (Tm Γ U) → Theory) → (Theory → Theory)
--   (▹ f) T = f (ctx ▷ U) (coe (U[] wk) vz)
--     where open Theory T

--   _►_ : (T : Theory)
--       → (A : Ty (Theory.ctx T))
--       → (∀ {Γ} → (Tm Γ (A [ {!!} ]ᵀ)) → Theory) → Theory
--   (theory Γ ► A) f = f {Γ ▷ A} {!vz!}

-- --   Int-Theory : Theory
-- --   Int-Theory = theory ∙
-- --     ▹ (λ N →             -- Define sort N
-- --     ▹ (λ Z →
-- --     theory (Theory.ctx _)))
-- --     -- ▹ λ Z → ?
-- -- --     ► El N λ z →       -- Define z : N
-- -- --       theory (Theory.ctx _)
-- -- -- --     ► Πⁱ N (El N [ wk ]ᵀ) λ s → -- Define s : N -> N
-- -- -- --     ▹ λ Z →             -- Define sort Z
-- -- -- --     ► (Πⁱ N (Πⁱ (N [ wk ]ᵀ) (El Z [ wk ]ᵀ [ wk ]ᵀ))) λ c → -- c : N -> N -> Z
-- -- -- --     theory (Theory.ctx _) -- Final resulting context

-- -- -- -- module Nat where
-- -- -- --   sig : Con
-- -- -- --   sig =
-- -- -- --     ∙ ▷ U -- N
-- -- -- --       ▷ El vz -- z
-- -- -- --       ▷ Πⁱ (coe (U[] wk) vz) (El (vs vz)) [ wk ]ᵀ -- s

-- -- -- -- module Int where
-- -- -- --   p : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)}
-- -- -- --     → U [ wk ]ᵀ [ wk ]ᵀ ≈ᵀ U {Γ = Γ ▷ A ▷ B}
-- -- -- --   p {Γ} {A} {B} = ≈T-trans (≈T-sym ([∘] U wk wk)) (U[] (wk ∘ wk))

-- -- -- --   q : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} {C : Ty (Γ ▷ A ▷ B)}
-- -- -- --     → U [ wk ]ᵀ [ wk ]ᵀ [ wk ]ᵀ ≈ᵀ U {Γ = Γ ▷ A ▷ B ▷ C}
-- -- -- --   q {Γ} {A} {B} {C} = ≈T-trans (≈T-trans (≈T-sym ([∘] (U [ wk ]ᵀ) wk wk)) (≈T-sym ([∘] U wk (wk ∘ wk)))) (U[] (wk ∘ wk ∘ wk))

-- -- -- --   sig : Con
-- -- -- --   sig = Nat.sig
-- -- -- --     ▷ U -- Z
-- -- -- --     ▷ Πⁱ (coe (U[] wk) (vs (coe q (vs (vs vz))))) (Πⁱ (coe p (vs vz)) (El (vs (vs vz)))) -- c : N → N → Z
-- -- -- --     ▷ {!!}
-- -- -- --     -- TODO: 
-- -- -- --     -- p : Π m : N. Π n : N. N
-- -- -- --     -- pz : Π n : N. Id n (p z n) n
-- -- -- --     -- ps : Π m : N. Π n : N. Id N (p (s m) n) (s (p m n))
-- -- -- --     -- q : Π m₁ : N. Π n₁ : N. Π m₂ : N. Π n₂ : N. Id N (plus m₁ n₂) (plus m₂ n₁)
-- -- -- --     --   → Id Z (c m₁ n₁) (c m₂ n₂) 
