open import QIT.Prelude

module QIT.Relation.WISC ⦃ pathElim* : PathElim ⦄ where

-- Adapted from fiore2022-quotient-inductive.

open import QIT.Prelude
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Ordinal
open import QIT.Prop
open import QIT.Function.Base hiding (_∘_)
open import QIT.Set.Base
open import QIT.Category.Preorder
open import QIT.Category.Set

IsWISC : ∀ {ℓ}
       → (A : Set ℓ)
       → (C : Set ℓ)
       → (W : C → Set ℓ)
       → (ℓ' : Level)
       → Prop (ℓ ⊔ lsuc ℓ')
IsWISC A C W ℓ' =
  ∀ (E : Set ℓ')
  → (q : E → A)
  → Surjective q
  → ∃ λ (c : C)
  → ∃ λ (f : W c → E)
  → Surjective (q ∘ f)

WISC : ∀ ℓ ℓ' → Prop (lsuc ℓ ⊔ lsuc ℓ')
WISC ℓ ℓ' = (A : Set ℓ)
     → ∃ λ (C : Set ℓ)
     → ∃ λ (W : C → Set ℓ)
     → IsWISC A C W ℓ'

IWISC : ∀ ℓ ℓ' → Prop (lsuc ℓ ⊔ lsuc ℓ')
IWISC ℓ ℓ' = (A : Set ℓ) (F : A → Set ℓ)
      → ∃ λ (C : Set ℓ)
      → ∃ λ (W : C → Set ℓ)
      → ∀ c → IsWISC (F c) C W ℓ'

WISC→IWISC : (∀ ℓ ℓ' → WISC ℓ ℓ') → (∀ ℓ ℓ' → IWISC ℓ ℓ')
WISC→IWISC wisc ℓ ℓ' A B with wisc ℓ (lsuc ℓ' ⊔ lsuc ℓ) A
... | ∃i C , ∃i D , wCD = matchp (wCD E p surj-p) (λ where
  (∃i c , ∃i f , surj-p∘f) →
    let C' : Set ℓ
        C' = {!!}
        D' : C' → Set ℓ
        D' = {!!}
        w' : ∀ c' → IsWISC (D' c') C' D' ℓ'
        w' = {!!}
    in ∃i C' , ∃i D' , w')
  where
  E : Set _
  E = Σ A λ x
    → Σ (Set ℓ) λ F₀
    → ΣP (F₀ → Set ℓ) λ F₁
    → IsWISC (B x) F₀ F₁ ℓ'
  p : E → A
  p (x , F₀ , F₁ , wF) = x
  surj-p : Surjective p
  surj-p x with wisc ℓ ℓ' (B x)
  ... | ∃i F₀ , ∃i F₁ , wF =
    ∃i (x , F₀ , F₁ , wF) , ≡.refl
    
  -- where
  -- f : (a : A)
  --   → (E : Set ℓ)
  --   → (q : E → F a)
  --   → Surjective q
  --   → ∃ λ (_ : C)
  --   → ∃ λ f → (y : F a)
  --   → ∃ (λ x → q (f x) ≡ y)
  -- f a E q surj-q with w E {!!} {!!}
  -- ... | u = {!!}

  
WeakAC : ∀ {ℓ} → (A : Set ℓ) (C : Set ℓ) (W : C → Set ℓ)
       → IsWISC A C W {!!}
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
  ... | ∃i c , ∃i f , surj-p'f =
    ∃i c , ∃i (p' ∘ f) , ∃i (λ z → q' (f z)) , ∧i surj-p'f , v
    where
    v : (z : W c) → P ((p' ∘ f) z) (q' (f z))
    v z = f z .snd

-- module _ {ℓ} (iwisc : IWISC ℓ) where
--   WeakAC'
--     : ∀ (A : Set ℓ)
--     → ∃ λ (C : Set ℓ)
--     → ∃ λ (W : C → Set ℓ)
--     → (B : A → Set ℓ)
--     → (P : ∀ x → B x → Prop ℓ)
--     → (∀ x → ∃ (P x))
--     → ∃ λ (c : C)
--     → ∃ λ (p : W c → A)
--     → ∃ λ (q : ∀ z → B (p z))
--     → Surjective p
--     ∧ (∀ z → P (p z) (q z))
--   WeakAC' A with iwisc ⊤ˢ* (λ _ → A)
--   ... | ∃i C , ∃i W , w = ∃i C , ∃i W , u 
--     where
--     u : (B : A → Set ℓ) (P : (x : A) → B x → Prop ℓ) (ex : (x : A) → ∃ (P x))
--       → ∃ (λ (c : C)
--       → ∃ (λ (p : W c → A)
--       → ∃ (λ (q : (z : W c) → B (p z))
--       → ((y : A) → ∃ (λ x → p x ≡ y))
--       ∧ ((z : W c) → P (p z) (q z)))))
--     u B P ex = WeakAC A C W (w tt*) B P ex
