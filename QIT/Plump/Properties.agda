open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Properties
open import QIT.Prop.Logic
import QIT.Container.Base as W
open W hiding (sup)
open import QIT.Setoid

open import QIT.Plump.Extensional as Plump

module QIT.Plump.Properties
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  (Plump : ∀ {ℓX} → Plump.InitialAlgebra S P ℓX)
  where

module _ {ℓX : Level} where
  open InitialAlgebra (Plump {ℓX}) public

Zᴬ' : Algebra S P (ℓS ⊔ ℓP)
Zᴬ' = Zᴬ {ℓ0}

  


-- open import QIT.Function.Base
-- open import QIT.Relation.Subset
-- open import QIT.Relation.Binary
-- open import QIT.Category.Preorder Z ≤p

-- ↓_ = ↓≤_

-- inc↓ : ∀ {α β} → α ≤ β → ↓ α → ↓ β 
-- inc↓ p γ = γ .fst , ≤≤ p (γ .snd)

-- CanonicalSurjection : ∀ {α β} → α ≤ β → ↓ β → ↓ α
-- CanonicalSurjection {α} p (γ , γ≤β) = (α ∧ᶻ γ) , ∧≤₁

-- -- swan2022 4.1
-- isSurjectionCanonicalSurjection : ∀ {α β} → (p : α ≤ β) → Surjective (CanonicalSurjection p)
-- isSurjectionCanonicalSurjection {α} {β} p (γ , γ≤α) =
--   ∣ inc↓ p (γ , γ≤α) , ΣP≡ _ _ q ∣
--   where
--   q : α ∧ᶻ γ ≡ γ
--   q = ≤antisym ∧≤₂ (∧-lim γ≤α (≤refl γ))

-- -- Too strong constructively. Use Acc instead?
-- record IsWellOrder {ℓA ℓR} (A : Set ℓA) (R : A → A → Prop ℓR) : Prop (lsuc ℓS ⊔ ℓA ⊔ ℓR) where
--   field
--     minSet : ∀ (S : A → Prop ℓS) → ∃ S
--            → ∃ {A = ΣP A S} λ (x , xs) → ∀ ((y , ys) : ΣP A S) → R y x 
     

-- open import QIT.Category.Equivalence
-- record IsRegular (κ : Z) : Prop (ℓS ⊔ ℓP) where
--   field
--     regular : ∀ α → α < κ → Equivalence (PreorderCat↓ α) (PreorderCat↓ κ) → ⊥p
