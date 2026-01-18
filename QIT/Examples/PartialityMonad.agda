module QIT.Examples.PartialityMonad where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)

mutual
  data PM : Set where
    ⊤ ⊥ : PM
    ⋁ : (a : ℕ → PM) → (∀ i → a i ≤ a (suc i)) → PM

  data _≤_ : PM → PM → Prop where
    ≤refl : ∀ x → x ≤ x
    ≤trans : ∀ x y z → x ≤ y → y ≤ z
    ⊥≤ : ∀ x → ⊥ ≤ x
    ≤⋁ : ∀ a p i → a i ≤ ⋁ a p
    ⋁≤ : ∀ a p x → (∀ i → a i ≤ x) → ⋁ a p ≤ x

  data _≈_ : PM → PM → Prop where
    ≈antisym : ∀ x y → x ≤ y → y ≤ x → x ≈ y

  -- ⊤ ⊥ : PM
  -- lub : (a : ℕ → PM) → (∀ i → a i ≡ ⊤ → a (suc i) ≡ ⊤) → PM
