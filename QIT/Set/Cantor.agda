open import QIT.Prelude
open import QIT.Prop

module QIT.Set.Cantor
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.Function.Base
open import QIT.Relation.Subset

Represents
  : ∀ {ℓ} (L : Set ℓ)
  → (L → L → Prop ℓ)
  → L
  → (L → Prop ℓ)
  → Prop _
Represents L R a P =
  ∀ x → R a x ⇔ P x

WeakSurj : ∀ {ℓ}
  (L : Set ℓ)
  → (L → L → Prop ℓ)
  → Prop _
WeakSurj L R =
  ∀ P → ∃ λ a → Represents L R a P

cantor : ∀ {ℓ}
  (L : Set ℓ)
  (R : L → L → Prop ℓ)
  → ¬ WeakSurj L R
cantor L R surj with surj (λ x → ¬ R x x)
... | ∃i a h = bad
  where
  ha : R a a ⇔ ¬ R a a
  ha = h a

  not-raa : ¬ R a a
  not-raa raa = ∧e₁ ha raa raa

  raa : R a a
  raa = ∧e₂ ha not-raa

  bad : ⊥
  bad = not-raa raa
