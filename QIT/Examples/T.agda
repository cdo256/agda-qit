open import QIT.Prelude

module QIT.Examples.T ⦃ a!c* : A!C ⦄ where

-- open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥') hiding (_≟_)
-- open import QIT.Relation.Subset
-- import Data.Nat as ℕ
-- open ℕ using (ℕ; zero; suc)
-- import Data.Bool as 𝔹 
-- open 𝔹 using (Bool; false; true)

-- import Data.Integer as ℤ 
-- open ℤ using (ℤ)

module _(I : Set) where

  mutual

    data T : Set where
        leaf : T
        node : (I → T) → T

  data _≤_ : T → T → Prop where
    ⊥≤ : ∀ {x} → leaf ≤ x
    ≤node : ∀ f i → f i ≤ node f
    node≤ : ∀ f t → (∀ i → f i ≤ t) → node f ≤ t
    node : ∀ f g → (∀ i → f i ≤ g i) 
                → node f ≤ node g 

  data _≈_ : T → T → Prop where
    ≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y


