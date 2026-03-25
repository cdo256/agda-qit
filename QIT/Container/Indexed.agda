module QIT.Container.Indexed where

open import QIT.Prelude
open import QIT.Functor.Base
open import QIT.Category.Set
open import QIT.Category.Slice
open import Data.Nat

record ICont {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
  constructor icont
  field
    S : I → Set ℓ
    P : ∀ {i} → S i → Set ℓ
    J : ∀ {i} → {s : S i} → P s → I -- child indices

module _ {ℓ} {I : Set ℓ} (C : ICont I) where
  open ICont C

  ⟦_⟧ : (I → Set ℓ) → (I → Set ℓ)
  ⟦_⟧ X i = Σ (S i) λ s → ∀ (p : P s) → X (J p)

  data IW : I → Set ℓ where
    isup : ∀ i → ⟦_⟧ IW i → IW i

  elim : ∀ {ℓ'} (M : ∀ i → IW i → Set ℓ')
      → (α : ∀ i s f → (∀ (p : P s) → M (J p) (f p)) → M i (isup i (s , f)))
      → ∀ i (w : IW i) → M i w
  elim M α i (isup i (s , f)) = α i s f (λ (p : P s) → elim M α (J p) (f p))

Fin : ICont ℕ
Fin = icont S P J
  where
  S : ℕ → Set
  S zero = ⊥
  S (suc x) = ⊤ ⊎ ⊤
  P : ∀ {i} → S i → Set
  P {suc i} (inj₁ tt) = ⊥ -- fzero
  P {suc i} (inj₂ tt) = ⊤ -- fsuc
  J : ∀ {i} {s : S i} → P s → ℕ
  J {suc i} {inj₂ tt} tt = i

Vec : (A : Set) → ICont ℕ
Vec A = icont S P J
  where
  S : ℕ → Set
  S zero = ⊥
  S (suc x) = A
  P : ∀ {i} → S i → Set
  P {suc i} a = ⊤
  J : ∀ {i} {s : S i} → P s → ℕ
  J {suc i} {a} tt = i
