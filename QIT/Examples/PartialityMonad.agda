module QIT.Examples.PartialityMonad where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥') hiding (_≟_)
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

import Data.Integer as ℤ
open ℤ using (ℤ)

interleaved mutual
  data Seq : Set
  data PM : Set
  data _≤_ : PM → PM → Prop
  data _≈_ : PM → PM → Prop

  data PM where
    η : Bool → PM
    ⊥ : PM
    ⨆ : (a : Seq) → PM
    ⟦_⟧ : Seq → (ℕ → PM)

  data Seq where
    _,_ : (f : ℕ → PM) → ((i : ℕ) → f i ≤ f (suc i)) → Seq

  data _≤_ where
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ⊥≤ : ∀ {x} → ⊥ ≤ x
    ≤⨆ : ∀ a i → ⟦ a ⟧ i ≤ ⨆ a
    ⨆≤ : ∀ a x → (∀ i → ⟦ a ⟧ i ≤ x) → ⨆ a ≤ x
    inc : (a : Seq) → ∀ i → ⟦ a ⟧ i ≤ ⟦ a ⟧ (suc i)

  data _≈_ where
    ≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

≤cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ≤ y → x' ≤ y'
≤cong (≈antisym x≤x' x'≤x) (≈antisym y≤y' y'≤y) x≤y = ≤trans x'≤x (≤trans x≤y y≤y')
≈refl : ∀ {x} → x ≈ x
≈refl = ≈antisym ≤refl ≤refl
≈sym : ∀ {x y} → x ≈ y → y ≈ x
≈sym (≈antisym p q) = ≈antisym q p
≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈trans (≈antisym p q) (≈antisym r s) = ≈antisym (≤trans p r) (≤trans s q)
