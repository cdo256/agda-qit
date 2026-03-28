module QIT.Examples.PartialityMonad.Direct where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

interleaved mutual
  infix 4 _≤_ _≈_
  data A⊥ : Set
  data _≤_ : A⊥ → A⊥ → Set
  data _≈_ : A⊥ → A⊥ → Set

  data _ where
    η : Bool → A⊥
    ⊥ : A⊥
    ⨆ : (a : ℕ → A⊥) (a-inc : ∀ i → a i ≤ a (suc i)) → A⊥
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ⊥≤ : ∀ {x} → ⊥ ≤ x
    ≤⨆ : ∀ a a-inc i → a i ≤ ⨆ a a-inc
    ⨆≤ : ∀ a a-inc x → (∀ i → a i ≤ x) → ⨆ a a-inc ≤ x
    ≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

record Algebra : Set₁ where
  infix 4 _≤ᴬ_ _≈ᴬ_

  field
    A⊥ᴬ : Set
    _≤ᴬ_ : A⊥ᴬ → A⊥ᴬ → Set
    _≈ᴬ_ : A⊥ᴬ → A⊥ᴬ → Set

    ηᴬ : Bool → A⊥ᴬ
    ⊥ᴬ : A⊥ᴬ
    ⨆ᴬ : (a : ℕ → A⊥ᴬ) → (a-inc : ∀ i → a i ≤ᴬ a (suc i)) → A⊥ᴬ
    ≤reflᴬ : ∀ {x} → x ≤ᴬ x
    ≤transᴬ : ∀ {x y z} → x ≤ᴬ y → y ≤ᴬ z → x ≤ᴬ z
    ⊥≤ᴬ : ∀ {x} → ⊥ᴬ ≤ᴬ x
    ≤⨆ᴬ : ∀ a a-inc i → a i ≤ᴬ ⨆ᴬ a a-inc
    ⨆≤ᴬ : ∀ a a-inc x → (∀ i → a i ≤ᴬ x) → ⨆ᴬ a a-inc ≤ᴬ x
    ≈antisymᴬ : ∀ {x y} → x ≤ᴬ y → y ≤ᴬ x → x ≈ᴬ y
  

module Properties where
  ≤cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ≤ y → x' ≤ y'
  ≤cong (≈antisym x≤x' x'≤x) (≈antisym y≤y' y'≤y) x≤y = ≤trans x'≤x (≤trans x≤y y≤y')
  ≈refl : ∀ {x} → x ≈ x
  ≈refl = ≈antisym ≤refl ≤refl
  ≈sym : ∀ {x y} → x ≈ y → y ≈ x
  ≈sym (≈antisym p q) = ≈antisym q p
  ≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  ≈trans (≈antisym p q) (≈antisym r s) = ≈antisym (≤trans p r) (≤trans s q)
