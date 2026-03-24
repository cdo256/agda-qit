module QIT.Examples.WFTree where

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

import Data.Bool as 𝟚
open 𝟚
  using (true; false) renaming (Bool to 𝟚) 
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

module _ ( _≟ᵗ_ : ∀ {s} → Discrete (Pᵀ s)) where
  record StepInj {a f i j s t p q π₁ π₂}
    (r : step {a} {f} i s p π₁ ≡ step j t q π₂) : Set where
    field
      index : i ≡ j
      tree  : s ≡ t
      π     : subst Path tree π₁ ≡ π₂

  step-inj : ∀ {a f i j s t p q π₁ π₂} 
           → (r : step {a} {f} i s p π₁ ≡ step j t q π₂) → StepInj r
  step-inj ≡.refl = record { index = ≡.refl ; tree = ≡.refl ; π = ≡.refl }

  -- We define a helper that uses matching on refl to force K-unification
  -- of the proof witnesses p and q.
  step-cong : ∀ {a f i s t p q π₁ π₂} 
            → (s≡t : s ≡ t) 
            → (π-eq : subst Path s≡t π₁ ≡ π₂)
            → step {a} {f} i s p π₁ ≡ step i t q π₂
  step-cong {p = p} {q = q} ≡.refl ≡.refl with isSetSet p q
  ... | ≡.refl = ≡.refl

  _≟ᵖ_ : ∀ {t} → Discrete (Path t)
  root t ≟ᵖ root .t = yes ≡.refl
  root _ ≟ᵖ step _ _ _ _ = no (λ ())
  step _ _ _ _ ≟ᵖ root _ = no (λ ())
  step {a} {f} i s p π₁ ≟ᵖ step {a} {f} j t q π₂ with i ≟ᵗ j
  ... | no i≠j = no (λ r → i≠j (step-inj r .StepInj.index))
  ... | yes ≡.refl with ≡.trans p (≡.sym q)
  ... | ≡.refl with π₁ ≟ᵖ π₂
  ... | yes ≡.refl = yes (step-cong ≡.refl ≡.refl)
  ... | no π₁≠π₂ = no λ r → π₁≠π₂ (r' r)
    where 
    open ≡.≡-Reasoning
    r' : ∀ r → π₁ ≡ π₂
    r' r = begin
      π₁
        ≡⟨ ≡.sym (subst-uip (isSetSet (step-inj r .StepInj.tree) ≡.refl) π₁) ⟩
      subst Path (step-inj r .StepInj.tree) π₁
        ≡⟨ step-inj r .StepInj.π ⟩
      π₂ ∎

  -- module _ (t : T) where
  --   data _≤_ : Path t → Path t → Prop where
  --     ≤refl : ∀ {x} → x ≤ x
  --     ≤step : ∀ {x y} → ↑ x ≤ x → x ≤ y → ↑ x ≤ y

  --   ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  --   ≤trans ≤refl q = q
  --   ≤trans (≤step p q) r = ≤step p (≤trans q r)

  --   data _<_ : Path t → Path t → Prop where
  --     <step : ∀ {x y} → x ≢ root _ → ↑ x < x → x ≤ y → ↑ x < y

  --   <step' : (x y : Path t) → x < y → (x ≡p ↑ y) ∨ (x < ↑ y)
  --   <step' _ y (<step {u} u≢root ↑u<u u≤y) with {!x!} ≟ᵖ {!!}
  --   ... | w = {!!}

  --   W→WFTree : WFTree
  --   W→WFTree = record
  --     { A = Path t 
  --     ; ∙ = root _
  --     ; ↑ = ↑
  --     ; _≺_ = _<_
  --     ; ≺step = {!≺step!}
  --     ; ↑≺ = {!↑≺!}
  --     ; trans = {!<trans!}
  --     }
