module QIT.Relation.WISC where

-- Adapted from fiore2022-quotient-inductive.

open import QIT.Prelude
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Ordinal
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Set.Base
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Functor.Base

WISC : ∀ {ℓ} → (A : Set ℓ) (C : Set ℓ) (W : C → Set ℓ) → Prop _
WISC {ℓ} A C W =
  ∀ (E : Set ℓ)
  → (q : E → A)
  → Surjective q
  → ∃ λ (c : C)
  → ∃ λ (f : W c → E)
  → Surjective (q ∘ f)
  
WeakAC : ∀ {ℓ} → (A : Set ℓ) (C : Set ℓ) (W : C → Set ℓ)
       → WISC A C W
       → (B : A → Set ℓ)
       → (P : ∀ x → B x → Prop ℓ)
       → (∀ x → ∃ (P x))
       → ∃ λ (c : C)
       → ∃ λ (p : W c → A)
       → ∃ λ (q : ∀ z → B (p z))
       → Surjective p
       ∧ (∀ z → P (p z) (q z))
WeakAC A C W w B P e = wac
  where
  D : Set _
  D = ΣP (Σ A B) λ (x , y) → P x y
  p' : D → A
  p' ((x , _) , _) = x
  isSurjection-p' : Surjective p'
  isSurjection-p' x with e x
  ... | ∣ y , pxy ∣ = ∣ (((x , y) , pxy) , ≡.refl) ∣
  q' : ∀ z → B (p' z)
  q' ((_ , b) , _) = b
  u : ∃ λ (c : C) → ∃ λ (f : W c → D) → Surjective (p' ∘ f)
  u = w D p' isSurjection-p'
  wac : ∃ (λ (c : C) → ∃ (λ p → ∃ (λ q → Surjective p ∧ ((z : W c) → P (p z) (q z)))))
  wac with w D p' isSurjection-p'
  ... | ∣ c , ∣ f , surj-p'f ∣ ∣ = ∣ c , ∣ p' ∘ f , ∣ (λ z → q' (f z)) , surj-p'f , v ∣ ∣ ∣
    where
    v : (z : W c) → P ((p' ∘ f) z) (q' (f z))
    v z = f z .snd

IWISC : ∀ ℓ → Prop (lsuc ℓ)
IWISC ℓ = (A : Set ℓ) (F : A → Set ℓ)
      → ∃ λ (C : Set ℓ)
      → ∃ λ (W : C → Set ℓ)
      → ∀ c → WISC (F c) C W

-- module _  where
--   open import QIT.Container.Base
--   open import Data.Nat
--   data S : Set where
--     zeroˢ : S
--     sucˢ : S
--     supˢ : S
--   data P : S → Set where
--     sucᵖ : P sucˢ
--     supᵖ : ℕ → P supˢ
--   BT : Set
--   BT = W S P

  

--   encode : BT → Ordinal ℓ0 ℓ0
--   encode (sup (zeroˢ , _)) = {!!}
--   encode (sup (sucˢ , x)) = {!!}
--   encode (sup (supˢ , x)) = {!!}

--   module _ (α : ℕ → Ordinal ℓ0 ℓ0) (r : ∀ n → ∃ λ t → encode t ≡ α n)  (wℕ : WISC ℕ S P) where
    
