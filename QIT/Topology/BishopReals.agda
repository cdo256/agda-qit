module QIT.Topology.BishopReals where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Integer as ℤ 
open ℤ using (ℤ; 0ℤ; 1ℤ)
import Data.Rational as ℚ
open ℚ using (ℚ; Positive; 0ℚ; 1ℚ)

postulate
  ℝ : Set
  _<_ : ℝ → ℝ → Prop

  <-irreflexive : ∀ (x : ℝ) → ¬ (x < x)
  <-cotransitive : ∀ (x y z : ℝ) → x < y → (x < z) ∨ (z < y)

  _+_ : ℝ → ℝ → ℝ
  _-_ : ℝ → ℝ → ℝ
  _*_ : ℝ → ℝ → ℝ
  ℚ→ℝ : ℚ → ℝ

0ℝ : ℝ
0ℝ = ℚ→ℝ 0ℚ
1ℝ : ℝ
1ℝ = ℚ→ℝ 1ℚ

1/1+ : (n : ℕ) → ℝ
1/1+ n = ℚ→ℝ (1ℤ ℚ./ suc n)

_≉_ : ℝ → ℝ → Prop
x ≉ y = (x < y) ∨ (y < x)

_≈_ : ℝ → ℝ → Prop
x ≈ y = ¬ (x < y) ∧ ¬ (y < x)

_≤_ : ℝ → ℝ → Prop
x ≤ y = ¬ (y < x)

postulate
  +-translate : ∀ (x y z : ℝ) → x < y → (x + z) < (y + z)
  *-scale : ∀ (x y : ℝ) → 0ℝ < x → 0ℝ < y → 0ℝ < (x * y)

  archimedean : ∀ (x y : ℝ) → x < y → ∃ λ (q : ℚ) → (x < ℚ→ℝ q) ∧ (ℚ→ℝ q < y)

  IsRegular : (ℕ → ℝ) → Prop
  lim : (s : ℕ → ℝ) → IsRegular s → ℝ
  lim-bound-upper : ∀ (s : ℕ → ℝ) (reg : IsRegular s)
                  → (n : ℕ) → (lim s reg - s n) ≤ 1/1+ n
  lim-bound-lower : ∀ (s : ℕ → ℝ) (reg : IsRegular s)
                  → (n : ℕ) → (0ℝ - 1/1+ n) ≤ (lim s reg - s n)

  -- Metric space properties
  ∣_-_∣₂ : (x y : ℝ) → ℝ
  0≤∣_-_∣₂ : (x y : ℝ) → 0ℝ ≤ ∣ x - y ∣₂
  ∣x-x∣₂≈0 : (x : ℝ) → ∣ x - x ∣₂ ≈ 0ℝ
  ∣∣₂-pos : (x y : ℝ) → x < y → 0ℝ < ∣ x - y ∣₂
  ∣∣₂-sym : (x y : ℝ) → ∣ x - y ∣₂ ≈ ∣ y - x ∣₂
  ∣∣₂-tri : (x y z : ℝ) →
    ∣ x - z ∣₂ ≤ (∣ x - y ∣₂ + ∣ y - z ∣₂)


module _ where
  [_,_] : (x y : ℝ) → ℝ → Prop
  [ x , y ] z = x ≤ z ∧ z ≤ y

  ]_,_[ : (x y : ℝ) → ℝ → Prop
  ] x , y [ z = x < z ∧ z < y

  Ball : (r c : ℝ) → ℝ → Prop
  Ball r c x = ∣ x - c ∣₂ < r
