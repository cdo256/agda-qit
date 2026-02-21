module QIT.Examples.WFTree (S : Set) (P : S → Set) where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Relation.WellFounded
open import QIT.Container.Base

record WFTree : Set₁ where
  field
    A : Set
    ∙ : A
    ↑ : A → A
    _≺_ : A → A → Prop -- is parent of

  _≪_ : A → A → Prop
  x ≪ y = (x ≡p y) ∨ x ≺ y

  field
    ≺step : ∀ x y → x ≺ y → x ≪ ↑ y
    ↑≺ : ∀ x → x ≡.≢ ∙ → ↑ x ≺ x
    trans : Transitive _≺_

open import Data.Bool as 𝟚
  hiding (T; if_then_else_; _∨_) renaming (Bool to 𝟚) 
open import QIT.Mobile.Base 𝟚

fork : T → T → T
fork x y = sup (n , λ b → 𝟚.if b then x else y) 

leaf : T
leaf = sup (l , λ())

data Path : T → Set where
  root : ∀ t → Path t
  step : ∀ {s f} i u → u ≡ f i → Path u → Path (sup (s , f))

Path→T : ∀ {t} → Path t → T
Path→T (root t) = t
Path→T (step i u q π) = Path→T π

t0 = leaf
t2 = fork leaf leaf
t3 = fork (fork leaf leaf) leaf

π1 : Path t3
π1 = step true _ ≡.refl (root _)
π2 : Path t3
π2 = step true _ ≡.refl (step false _ ≡.refl (root _))

t0-1 : (x : Path t0) → x ≡ root leaf
t0-1 (root t) = ≡.refl

↑ : ∀ {t} → Path t → Path t
↑ (root t) = root t
↑ (step {s} {f} i u q (root t)) = root (sup (s , f))
↑ (step {a} {f} i u q (step {b} {g} j s r π)) =
  step i u q (↑ (step {b} {g} j s r π))

_ : ↑ π1 ≡ root _ 
_ = ≡.refl

_ : ↑ π2 ≡ π1
_ = ≡.refl

module _ ( _≟ˢ_ : Discrete Sᵀ) ( _≟ᵗ_ : ∀ {s} → Discrete (Pᵀ s)) where
  record StepInj {a} {i j : Pᵀ a} {f : Pᵀ a → T} {s t p q π₁ π₂}
    (r : step {a} {f} i s p π₁ ≡ step j t q π₂) : Set where
    field
      index : i ≡ j
      tree : s ≡ t
      π : subst Path tree π₁ ≡ π₂

  step-inj : ∀ {a} {i j : Pᵀ a} {f : Pᵀ a → T} {s t p q π₁ π₂} (r : step {a} {f} i s p π₁ ≡ step j t q π₂) → StepInj r
  step-inj ≡.refl = record { index = ≡.refl ; tree = ≡.refl ; π = ≡.refl }

  _≟ᵖ_ : ∀ {t} → Discrete (Path t)
  root _ ≟ᵖ root _ = yes ≡.refl
  root _ ≟ᵖ step _ _ _ _ = no (λ ())
  step _ _ _ _ ≟ᵖ root _ = no (λ ())
  step {a} {f} i s p π₁ ≟ᵖ step {a} {f} j t q π₂
    with (i ≟ᵗ j)
  ... | no i≠j = no λ r → i≠j (step-inj r .StepInj.index)
  ... | yes ≡.refl with (≡.subst Path (≡.trans p (≡.sym q)) π₁ ≟ᵖ  π₂)
  ... | no π₁≠π₂ = no λ v → π₁≠π₂ let
    w = step-inj v .StepInj.π
    u : ≡.trans p (≡.sym q) ≡ step-inj v .StepInj.tree
    u = isSetSet (≡.trans p (≡.sym q)) (step-inj v .StepInj.tree)
    in ≡.trans (≡.cong (λ ○ → subst Path ○ π₁) u) w
  ... | yes ≡.refl = yes {!w (≡.trans p (≡.sym q))!}
    where
    open ≡.≡-Reasoning
    w : (s≡t : s ≡ t) (p≡q : subst (λ ○ → ○ ≡ f i) s≡t p ≡ q) → step i s p π₁ ≡ step i t q (subst Path s≡t π₁)
    w ≡.refl ≡.refl =
      step i s p π₁
        ≡⟨ ≡.refl ⟩
      step i t p π₁
        ≡⟨ ≡.dcong₂ (step i t) (isSetSet p q) v ⟩
      step i t q (subst Path ≡.refl π₁) ∎
      where
      v : subst (λ _ → Path s) (isSetSet p q) π₁ ≡ subst Path ≡.refl π₁
      v = ≡.cong (λ ○ → subst (λ _ → Path s) ○ π₁) (isSetSet (isSetSet p p) ≡.refl)

-- module _ (t : T) where
--   data _≺_ : Path t → Path t → Prop where
--     ≺step : ∀ x y → x ≺ y → ¬ (x ≡p ↑ y) → (x ≺ ↑ y)
--     ↑≺ : ∀ x → x ≡.≢ root _ → ↑ x ≺ x
--     trans : Transitive _≺_


--   W→WFTree : WFTree
--   W→WFTree = record
--     { A = Path t 
--     ; ∙ = root _
--     ; ↑ = ↑
--     ; _≺_ = _≺_
--     ; ≺step = λ x y π → {!!}
--     ; ↑≺ = ↑≺
--     ; trans = trans
--     }
