module QIT.IIT.Base where

open import QIT.Prelude
open import QIT.Functor.Base
open import QIT.Category.Set
open import QIT.Category.Slice
open import Data.Nat

record ICont {ℓ} : Set (lsuc ℓ) where
  field
    Sᴬ : Set ℓ
    Sᴮ : Set ℓ
    Pᴬᴬ : Sᴬ → Set ℓ
    Pᴬᴮ : Sᴬ → Set ℓ
    Jᴬᴮ : (s : Sᴬ) → (p : Pᴬᴬ s) → {!!}
    Pᴮᴬ : (s : Sᴮ) → {!!}

open ICont

--   data Con : Set
--   data Ty : Con → Set
-- 
--   data Con where
--     ∙ : Con
--     _▷_ : (Γ : Con) → Ty Γ → Con
-- 
--   data Ty where
--     ι : (Γ : Con) → Ty Γ
--     Π̇ : (Γ : Con) → (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ

ConTy : ICont
ConTy .Sᴬ = ⊤ ⊎ ⊤
ConTy .Sᴮ = ⊤ ⊎ ⊤
ConTy .Pᴬᴬ (inj₁ tt) = ⊥
ConTy .Pᴬᴬ (inj₂ tt) = {!!}
ConTy .Pᴬᴮ = {!!}
ConTy .Jᴬᴮ = {!!}
ConTy .Pᴮᴬ = {!!}

-- record
--   { Sᴬ = ⊤ ⊎ ⊤ -- ∙ , ▷
--   ; Sᴮ = ⊤ ⊎ ⊤ -- ι , π
--   ; Pᴬᴬ = {!!}
--   ; Pᴬᴮ = {!!}
--   ; Jᴬᴮ = {!!}
--   ; Pᴮᴬ = {!!} }

-- -- module _ {ℓ} {I : Set ℓ} (C : ICont I) where
-- --   open ICont C

-- --   ⟦_⟧ : (I → Set ℓ) → (I → Set ℓ)
-- --   ⟦_⟧ X i = Σ (S i) λ s → ∀ p → X (J s p)

-- --   data IW : I → Set ℓ where
-- --     isup : ∀ i → ⟦_⟧ IW i → IW i

-- --   elim : ∀ {ℓ'} (M : ∀ i → IW i → Set ℓ')
-- --       → (α : ∀ i s f → (∀ p → M (J s p) (f p)) → M i (isup i (s , f)))
-- --       → ∀ i (w : IW i) → M i w
-- --   elim M α i (isup i (s , f)) = α i s f (λ p → elim M α (J s p) (f p))

-- -- Fin : ICont ℕ
-- -- Fin = iw S P J
-- --   where
-- --   S : ℕ → Set
-- --   S zero = ⊥
-- --   S (suc x) = ⊤ ⊎ ⊤
-- --   P : ∀ {i} → S i → Set
-- --   P {suc i} (inj₁ tt) = ⊥ -- fzero
-- --   P {suc i} (inj₂ tt) = ⊤ -- fsuc
-- --   J : ∀ {i} → (s : S i) → P s → ℕ
-- --   J {suc i} (inj₂ tt) tt = i

-- -- Vec : (A : Set) → ICont ℕ
-- -- Vec A = iw S P J
-- --   where
-- --   S : ℕ → Set
-- --   S zero = ⊥
-- --   S (suc x) = A
-- --   P : ∀ {i} → S i → Set
-- --   P {suc i} a = ⊤
-- --   J : ∀ {i} → (s : S i) → P s → ℕ
-- --   J {suc i} a tt = i
