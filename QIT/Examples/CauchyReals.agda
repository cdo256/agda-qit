module QIT.Examples.CauchyReals where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥') hiding (_≟_)
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹 
open 𝔹 using (Bool; false; true)

import Data.Integer as ℤ 
open ℤ using (ℤ)

import Data.Rational as ℚ
open ℚ using (ℚ)

private
  _>0 : ℚ → Set
  _>0 = ℚ.Positive

record IsCauchy (s : ℕ → ℚ) : Set where
  field
    upper : ℕ → ℚ
    lower : ℕ → ℚ
    s>u : ∀ n → s n ℚ.< upper n
    l<s : ∀ n → lower n ℚ.< s n
    cauchy : ∀ ε → ε >0 → ∃ λ n → ∀ m → m ℕ.> n
           → ∥ ℚ.∣ upper m ℚ.- lower m ∣ ℚ.< ε ∥

ℝ = ΣP (ℕ → ℚ) (Trunc₁ IsCauchy)

data _≈_ : (a b : ℝ) → Prop where
  ≈bisim : ∀ a b → (∀ ε → ε >0 → ∃ λ n → ∀ m → m ℕ.> n
         → ∥ ℚ.∣ a .fst m ℚ.- b .fst m ∣ ℚ.< ε ∥) → a ≈ b
  
