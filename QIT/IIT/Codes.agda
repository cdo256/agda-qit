module QIT.IIT.Codes where

open import QIT.Prelude
open import Data.Nat.Base hiding (_+_)
open import Data.Fin.Base hiding (_+_)

-- data Con : Set

-- -- Simplification where each signature depends once on each prior Sig
-- Fam = ℕ

-- data Ty : Con → Set
-- data SP : ∀ (Γ : Con) (F : Fam) → Fin F → Set
-- data Sig : ∀ {Γ : Con} (F : Fam)
--          → ((i : Fin F) → SP Γ F i) → Set

-- data Con where
--   ∙ᶜ : Con
--   _▷ᵀ_ : (Γ : Con) → Ty Γ → Con

-- data SP where
--   𝟙 : ∀ Γ F i → SP Γ F i
--   -- sig-0 : ∀ Γ ∑ → SP Γ ∑ → SP Γ (sˢ ∑)
--   -- sig-suc : {!!}
  
data Con : Set
data Ty : Con → Set
data Tm : {Γ : Con} → Ty Γ → Set
data SP : Con → Set
data Subst : Con → Con → Set

infix 30 _[_]
_[_] : {Γ Δ : Con} → Ty Δ → Subst Γ Δ → Ty Γ 

data Con where
  ∙ : Con
  _▷_ : (Γ : Con) → Ty Γ → Con
  _▷⁺_ : (Γ : Con) → SP Γ → Con

data Ty where
  ι : ∀ {Γ} → Ty Γ
  𝟙 : ∀ {Γ} → Ty Γ
  Σ̇ : ∀ {Γ} → (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
  Π̇ : ∀ {Γ} → (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ

data Subst where  
  id : ∀ Γ → Subst Γ Γ 
  _,_ : ∀ {Γ Δ} {A : Ty Δ} → (σ : Subst Γ Δ) → (t : Tm (A [ σ ]))
      → Subst Γ (Δ ▷ A)

  
ι [ σ ] = ι
𝟙 [ σ ] = 𝟙 
Σ̇ A B [ σ ] = Σ̇ {!!} {!!}
Π̇ A B [ σ ] = {!!}

-- data Tm where
--   tẗ : ∀ {Γ} → Tm {Γ} 𝟙
--   λ̇ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)}
--     → Tm B → Tm (Π̇ A B) 
--   ＠̇ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)}
--      → Tm (Π̇ A B) → (t : Tm A) → Tm (B [ id Γ , t ])
--   _,̇_ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)}
--     → Tm A → Tm B → Tm (Σ̇ A B) 
--   fsẗ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)}
--     → (t : Tm (Σ̇ A B)) → Tm A
--   snd̈ : ∀ {Γ} → {A : Ty Γ} {B : Ty (Γ ▷ A)}
--     → (t : Tm (Σ̇ A B)) → Tm (B [ id Γ , fsẗ t ])

-- data SP where
--   tyᴬ : ∀ {Γ} → Ty Γ → SP Γ
--   Π̇ᴬ : ∀ {Γ} → (A : Ty Γ) (B : SP (Γ ▷ A)) → SP Γ
--   Σ̇ᴬ : ∀ {Γ} → (A : Ty Γ) (B : SP (Γ ▷ A)) → SP Γ

-- 𝟚 : ∀ {Γ} → Ty Γ 
-- 𝟚 = Σ̇ 𝟙 𝟙

-- _+ᴬ_ : ∀ {Γ} → SP Γ → SP Γ → SP Γ
-- X +ᴬ Y = Σ̇ᴬ 𝟚 {!!}
