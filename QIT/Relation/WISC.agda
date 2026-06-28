open import QIT.Prelude

module QIT.Relation.WISC ⦃ pathElim* : PathElim ⦄ where

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
  ... | ∃i y , pxy = ∃i (((x , y) , pxy)) , ≡.refl
  q' : ∀ z → B (p' z)
  q' ((_ , b) , _) = b
  u : ∃ λ (c : C) → ∃ λ (f : W c → D) → Surjective (p' ∘ f)
  u = w D p' isSurjection-p'
  wac : ∃ (λ (c : C) → ∃ (λ p → ∃ (λ q → Surjective p ∧ ((z : W c) → P (p z) (q z)))))
  wac with w D p' isSurjection-p'
  ... | ∃i c , ∃i f , surj-p'f = ∃i c , ∃i (p' ∘ f) , ∃i (λ z → q' (f z)) , ∧i surj-p'f , v
    where
    v : (z : W c) → P ((p' ∘ f) z) (q' (f z))
    v z = f z .snd

IWISC : ∀ ℓ → Prop (lsuc ℓ)
IWISC ℓ = (A : Set ℓ) (F : A → Set ℓ)
      → ∃ λ (C : Set ℓ)
      → ∃ λ (W : C → Set ℓ)
      → ∀ c → WISC (F c) C W
